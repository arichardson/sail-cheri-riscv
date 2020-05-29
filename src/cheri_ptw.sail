/* failure modes for address-translation/page-table-walks */

union PTW_Error = {
  PTW_Invalid_Addr  : unit,          /* invalid source address */
  PTW_Access        : unit,          /* physical memory access error for a PTE */
  PTW_Invalid_PTE   : unit,
  PTW_No_Permission : unit,
  PTW_Misaligned    : unit,          /* misaligned superpage */
  PTW_PTE_Update    : unit,          /* PTE update needed but not enabled */
  PTW_Ext_Error     : ext_ptw_error  /* parameterized for errors from extensions */
}

val ptw_error_to_str : PTW_Error -> string
function ptw_error_to_str(e) =
  match (e) {
    PTW_Invalid_Addr()   => "invalid-source-addr",
    PTW_Access()         => "mem-access-error",
    PTW_Invalid_PTE()    => "invalid-pte",
    PTW_No_Permission()  => "no-permission",
    PTW_Misaligned()     => "misaligned-superpage",
    PTW_PTE_Update()     => "pte-update-needed",
    PTW_Ext_Error(e)     => "extension-error"
  }

overload to_str = {ptw_error_to_str}

/*
 * I apologize for the confusion you have experienced if you have skipped over
 * this comment and read the body of this function first.  Hopefully these two
 * points resolve most of it:
 *
 * 1) While it may look like we're signaling that we must *always* raise
 * faults, translationException below can see whether the instruction
 * triggering the PTW is claiming to store an asserted tag, and will ignore our
 * result if that isn't so.
 *
 * 2) We analyse only the store-side component of ext_ptw here.  The PTW logic
 * cannot see into the data path, and so load-side responses, including traps,
 * must be handled by the instruction that initiated the translation.
 */
function ext_get_ptw_error(ext_ptw : ext_ptw) -> PTW_Error =
  match (ext_ptw.ptw_sc_mod) {

    /*
     * This is confusing: PTW_No_Permission() is never used as such, but just
     * dodges the pattern matches in translationException, below.
     */
    PTW_SCM_OK   => PTW_No_Permission(),

    PTW_SCM_TRAP => PTW_Ext_Error(AT_CAP_ERR)
  }

/* conversion of these translation/PTW failures into architectural exceptions */
function translationException(a : AccessType(ext_access_type), f : PTW_Error) -> ExceptionType = {
  let e : ExceptionType =
  match (a, f) {

    /* Tag-asserting stores can raise CHERI page faults. */
    (Write(Cap), PTW_Ext_Error(AT_CAP_ERR))     => E_Extension(EXC_SAMO_CAP_PAGE_FAULT),

    /*
     * XXX ReadWrite(Cap) does not provide enough information to distinguish
     * between a tag-clearing store and tag-asserting store in the presence of
     * a tag-capable load, or a tag-asserting store in the case of a
     * tag-incapable load.  (That is, it only clearly distinguishes a
     * tag-incapable load with a tag-clearing store from every other option.)
     * Groundwork for fixing this exists in the sail RISC-V model, but we have
     * not yet caught up to that point.  Fortunately, we don't actually have
     * amoswap.c yet, so this is not observably wrong.
     */
    (ReadWrite(Cap), PTW_Ext_Error(AT_CAP_ERR)) => E_Extension(EXC_SAMO_CAP_PAGE_FAULT),

    /*
     * XXX Read(_) and Execute() should never result in an ext_ptw value that
     * gets mapped to PTW_Ext_Error(_); see checkPTEPermission.  Should we
     * assert that here?
     */

    /* For other exceptions, Cap accesses fault similar to Data accesses below. */
    (ReadWrite(Cap), PTW_Access())  => E_SAMO_Access_Fault(),
    (ReadWrite(Cap), _)             => E_SAMO_Page_Fault(),
    (Read(Cap), PTW_Access())       => E_Load_Access_Fault(),
    (Read(Cap), _)                  => E_Load_Page_Fault(),
    (Write(Cap), PTW_Access())      => E_SAMO_Access_Fault(),
    (Write(Cap), _)                 => E_SAMO_Page_Fault(),

    (ReadWrite(Data), PTW_Access()) => E_SAMO_Access_Fault(),
    (ReadWrite(Data), _)            => E_SAMO_Page_Fault(),
    (Read(Data), PTW_Access())      => E_Load_Access_Fault(),
    (Read(Data), _)                 => E_Load_Page_Fault(),
    (Write(Data), PTW_Access())     => E_SAMO_Access_Fault(),
    (Write(Data), _)                => E_SAMO_Page_Fault(),

    (Execute(), PTW_Access())       => E_Fetch_Access_Fault(),
    (Execute(), _)                  => E_Fetch_Page_Fault()
  } in {
/*  print_mem("translationException(" ^ a ^ ", " ^ f ^ ") -> " ^ e); */
    e
  }
}
