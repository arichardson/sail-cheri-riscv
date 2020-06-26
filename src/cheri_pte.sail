/* PTE attributes, permission checks and updates */

type pteAttribs = bits(8)

bitfield PTE_Bits : pteAttribs = {
  D : 7,
  A : 6,
  G : 5,
  U : 4,
  X : 3,
  W : 2,
  R : 1,
  V : 0
}

/*
 * Reserved PTE bits used by extensions on RV64.
 *
 * For capability store the behaviors are as follows.
 *
 *   CW  CD  Action
 *
 *    0   X    Trap on tagged capability store
 *    1   0    CAS the PTE to CW=1, CD=1 (i.e., set both bits) or trap
 *    1   1    Permit tagged capability store
 *
 * The CW/CD pair is akin to RVnn's W/D bits.
 *
 * The CW=1 CD=0 behavior is described as a CAS of the PTE to close race
 * conditions, much as with W and D.  Should the TLB have this state cached and
 * then observe a CW=1 CD=1 PTE, no PTE write is necessary.  On the other hand,
 * if CW=0 is observed, the store operation must trap.
 *
 * The intended semantics for capability loads are as follows.
 *
 *   CR  CR_Mod CR_Gen  Action
 *
 *    0     0      0    Capability loads strip tags
 *    0     1      0    Capability loads trap (on set tag)
 *    0     X      1    [Reserved]
 *
 *    1     0      0    Capability loads succeed: no traps or tag clearing
 *    1     0      1    [Reserved]
 *    1     1      G    Capability loads trap if G mismatches sccsr.gclg[su],
 *                         where the compared bit is keyed off of this PTE's U.
 *
 * DATA DEPENDENCE: We anticipate that the data-dependent traps may be
 * uncomfortable for some architectures, and we therefore permit
 * microarchitectures to trap in data-independent ways (i.e., any instruction
 * capable of loading a tag may raise a trap even if the tag is not set).
 * However, microarchitectures must gate their capability-load traps on the PTE
 * bits (and sccsr.gclg[su]); that is, we permit relaxing only the dependence
 * on the tag bit itself.
 *
 * SV32: There are no extension bits available, so we hard-code the result to
 * CW=1 CD=1, LC=1, LC_Mod=0, LC_Gen=0
 */
type extPte = bits(10)

bitfield Ext_PTE_Bits : extPte = {
  CapWrite     : 9, /* Permit capability stores */
  CapRead      : 8, /* Permit capability loads */
  CapDirty     : 7, /* Capability Dirty flag */
  CapRead_Mod  : 6, /* Modify capability load prohibition; see above table */
  CapRead_Gen  : 5, /* When load-cap gens. are in use, the "local" gen. bit */
}

/*
 * CapWrite     = 1,
 * CapRead      = 1,
 * CapDirty     = 1,
 * LoadCap_Mod  = 0,
 * LoadCap_Gen  = 0,
 * bits 0 .. 4  = 0
 */
let default_sv32_ext_pte : extPte = 0b1110000000

function isPTEPtr(p : pteAttribs, ext : extPte) -> bool = {
  let a = Mk_PTE_Bits(p);
  a.R() == 0b0 & a.W() == 0b0 & a.X() == 0b0
}

function isInvalidPTE(p : pteAttribs, ext : extPte) -> bool = {
  let a = Mk_PTE_Bits(p);
  a.V() == 0b0 | (a.W() == 0b1 & a.R() == 0b0)
}

union PTE_Check = {
  PTE_Check_Success : ext_ptw,
  PTE_Check_Failure : ext_ptw
}

val checkPTEPermission_SC_caveat : Ext_PTE_Bits -> ext_ptw_scm
function checkPTEPermission_SC_caveat(e) =
  if e.CapWrite() == 0b1 then PTW_SCM_OK else PTW_SCM_TRAP

/*
 * Assuming we're allowed to load from this page, modulate our cap response
 */
val checkPTEPermission_LC_caveat : (PTE_Bits, Ext_PTE_Bits) -> ext_ptw_lcm effect {rreg, escape}
function checkPTEPermission_LC_caveat(p, e) =
  if e.CapRead() == 0b0
  then match (e.CapRead_Gen(), e.CapRead_Mod()) {
         (0b1, _)  => not_implemented("Reserved PTE extension bits: !LC but Gen"),
         (_, 0b0)  => PTW_LCM_CLR   /* Clear tag for "unmodified" no-LC case */,
         (_, 0b1)  => PTW_LCM_TRAP  /* Trap on tag load for "modified" no-LC case */
      }
  else if e.CapRead_Mod() == 0b0
       then { if e.CapRead_Gen() == 0b0
              then PTW_LCM_OK /* Unmodified LC case: go ahead */
              else not_implemented("Reserved PTE extension bits: LC, !LC_Mod but Gen")
       }
       else { /* With CapRead_Mod on with LC, use Gen */
              let gclg : bits(1) = if p.U() == 0b1 then sccsr.gclgu() else sccsr.gclgs();
              if e.CapRead_Gen() == gclg
              then PTW_LCM_OK
              else PTW_LCM_TRAP
       }

function checkPTEPermission(ac : AccessType(ext_access_type), priv : Privilege, mxr : bool, do_sum : bool, p : PTE_Bits, ext : extPte, ext_ptw : ext_ptw) -> PTE_Check = {
  /*
   * Although in many cases MXR doesn't make sense for capabilities, we honour
   * it for three reasons:
   *
   * 1. It provides uniformity rather than giving strange and surprising edge cases.
   *
   * 2. The tag-dependence of stores is achieved by passing Data in for untagged
   *    capabilities. Thus, not honouring MXR for capabilities would result in
   *    differences in whether MXR had an effect based on the tag.
   *
   * 3. It's simpler to implement yet still safe (LC is unaffected by MXR).
   */
  let base_succ : bool =
  match (ac, priv) {
    (Read(_),      User)       => p.U() == 0b1 & (p.R() == 0b1 | (p.X() == 0b1 & mxr)),
    (Write(_),     User)       => p.U() == 0b1 & p.W() == 0b1,
    (ReadWrite(_), User)       => p.U() == 0b1 & p.W() == 0b1 & (p.R() == 0b1 | (p.X() == 0b1 & mxr)),
    (Execute(),    User)       => p.U() == 0b1 & p.X() == 0b1,

    (Read(_),      Supervisor) => (p.U() == 0b0 | do_sum) & (p.R() == 0b1 | (p.X() == 0b1 & mxr)),
    (Write(_),     Supervisor) => (p.U() == 0b0 | do_sum) & p.W() == 0b1,
    (ReadWrite(_), Supervisor) => (p.U() == 0b0 | do_sum) & p.W() == 0b1 & (p.R() == 0b1 | (p.X() == 0b1 & mxr)),
    (Execute(),    Supervisor) => p.U() == 0b0 & p.X() == 0b1,

    (_,            Machine)    => internal_error("m-mode mem perm check")
  };

  let e = Mk_Ext_PTE_Bits(ext);
  let scav = checkPTEPermission_SC_caveat(e);
  let lcav = checkPTEPermission_LC_caveat(p, e);
  let (succ, ext_ptw') : (bool, ext_ptw) =
  match (base_succ, ac) {
    /* Base translation exceptions take priority over CHERI exceptions */
    (false, _)                    => (false, init_ext_ptw),

    (true,  Read(Cap))            => (true, ext_ptw_join_lcm(ext_ptw, lcav)),
    (true,  Write(Cap))           => (true, ext_ptw_join_scm(ext_ptw, scav)),
    (true,  ReadWrite(Data,Cap))  => (true, ext_ptw_join_scm(ext_ptw, scav)),
    (true,  ReadWrite(Cap,Data))  => (true, ext_ptw_join_lcm(ext_ptw, lcav)),
    (true,  ReadWrite(Cap,Cap))   => (true, ext_ptw_join_scm(ext_ptw_join_lcm(ext_ptw, lcav), scav)),

    (true,  Read(Data))           => (true, ext_ptw),
    (true,  Write(Data))          => (true, ext_ptw),
    (true,  ReadWrite(Data,Data)) => (true, ext_ptw),
    (true,  Execute())            => (true, ext_ptw)
  };

  if succ then PTE_Check_Success(ext_ptw') else PTE_Check_Failure(ext_ptw')
}

function update_PTE_Bits(p : PTE_Bits, a : AccessType(ext_access_type), ext : extPte) -> option((PTE_Bits, extPte)) = {
  // dirty bit
  let update_d = p.D() == 0b0 & (match a {
                                  Execute()    => false,
                                  Read(_)      => false,
                                  Write(_)     => true,
                                  ReadWrite(_,_) => true
                                });

  // accessed bit
  let update_a = p.A() == 0b0;

  let eb = Mk_Ext_PTE_Bits(ext);

  // store cap bits
  let update_cd = eb.CapWrite() == 0b1 & eb.CapDirty() == 0b0
                  & (match a {
                     Write(Cap)     => true,
                     ReadWrite(_,Cap) => true,
                     _              => false
                  });

  if update_d | update_a | update_cd then {
    let np = update_A(p, 0b1);
    let np = if update_d then update_D(np, 0b1) else np;
    let ne = if update_cd then update_CapDirty(0b1) else eb;
    Some(np, ne.bits())
  } else None()
}
