/// `Fold`: the pure half of resume-time context folding. What these pin is
/// the SAFETY of the cut (a kept tail may never begin with an orphan tool
/// result, and the digest must never be the only copy of anything), not the
/// prose of the digest.
///
/// The bug these exist for: `Store.load_history_seq` hands a resume EVERY
/// committed history block, and `set_session` zeroes `last_context`, so the
/// first resumed turn re-uploads the whole session -- and autocompact then
/// re-renders that same history into its own summarization prompt, paying
/// for it twice before anything shrinks.
use weaver::fold {
    Fold.tail_budget, Fold.fits, Fold.digest_body, Fold.digest_note,
    Fold.pointer_line, Fold.fold_session,
}
use weaver::compact {Compact.keep_budget, Compact.threshold}
use shuttle::message {Message, Usage}
use shuttle::message_types {Role, Content}
use shuttle::session {Session}
use shuttle::provider {ProviderConfig, Wire}
use std::path {Path, Path.of}
use std::list {}
use json::json {Json, Json.make_null}

def test_cfg : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "K", max_tokens := 8, wire := Wire.mock, thinking := false }

def usage0 : Usage := { input_tokens := 0, output_tokens := 0, cached_tokens := 0 }

def history_dir : Path :=
    match Path.of "/tmp/weaver_fold_probe/sessions/s-fold" {
        Result.err _ => Path.path "/tmp/weaver_fold_probe",
        Result.ok p => p,
    }

def session_with (history : List Message) : Session :=
    { config := test_cfg, system_prompt := "sys", tools := List.empty, history := history, turns := 0, spent := usage0 }

def user_msg (s : String) : Message :=
    { role := Role.user, content := [Content.text s] }

def assistant_msg (s : String) : Message :=
    { role := Role.assistant, content := [Content.text s] }

def tool_msg (s : String) : Message :=
    { role := Role.tool, content := [Content.tool_result "call_1" s false] }

def big (n : I64) : String := String.repeat "x" n

/// The digest never gets its own budget: it must not scale with the
/// number of dropped messages any more than a summary would.
#[test]
def test_tail_budget_is_a_share_of_the_window : Bool :=
    Bool.and (Fold.tail_budget 128000i64 80i64 == Compact.keep_budget (Compact.threshold 128000i64 80i64))
        (Bool.and (Fold.tail_budget 0i64 80i64 == 0i64) (Fold.tail_budget 128000i64 0i64 == 0i64))

#[test]
def test_fits_is_the_complement_of_over_budget : Bool :=
    let ms : List Message := [user_msg "hi", assistant_msg "there"] in
    Bool.and (Fold.fits ms 1000000i64) (Bool.not (Fold.fits ms 1i64))

/// A session that already fits its tail budget is not folded AT ALL: the
/// restored history must replay byte-for-byte, or a resume would silently
/// rewrite a short session's context.
#[test]
def test_a_small_session_is_not_folded : Bool :=
    let s : Session := session_with [user_msg "one", assistant_msg "two"] in
    match Fold.fold_session s history_dir 1i64 1000000i64 {
        Option.none => true,
        Option.some _ => false,
    }

/// The cut itself: only the older prefix becomes the digest, and the
/// newest USER turn survives verbatim.
#[test]
def test_a_large_session_folds_only_the_prefix : Bool :=
    let old : List Message := [user_msg (big 4000i64), assistant_msg (big 4000i64), tool_msg (big 4000i64)] in
    let recent : List Message := [user_msg "the newest ask", assistant_msg "the newest answer"] in
    let s : Session := session_with (List.append old recent) in
    match Fold.fold_session s history_dir 1i64 200i64 {
        Option.none => false,
        Option.some out =>
            Bool.and (List.length out.session.history < List.length s.history)
                (Bool.and (List.length out.session.history == 3i64) (kept_tail_ok out.session.history)),
    }

/// The digest is the folded history's head, so the KEPT TAIL is everything
/// after it. A kept tail is valid when it is empty (the digest alone is the
/// whole context) or begins at a USER message -- never at an orphan tool
/// result, never at the second half of a tool_use/tool_result pair (both
/// wires reject a tail that begins with one).
def kept_tail_ok (history : List Message) : Bool :=
    match history {
        List.empty => false,
        List.cons _ rest => match rest {
            List.empty => true,
            List.cons m _ => match m.role { Role.user => true, _ => false },
        },
    }

#[test]
def test_the_kept_tail_never_keeps_a_dangling_tool_result : Bool :=
    let old : List Message := [user_msg (big 4000i64), assistant_msg (big 4000i64)] in
    let orphan_prone : List Message := [user_msg "short ask", tool_msg (big 4000i64)] in
    let s : Session := session_with (List.append old orphan_prone) in
    match Fold.fold_session s history_dir 1i64 200i64 {
        Option.none => false,
        Option.some out => kept_tail_ok out.session.history,
    }

/// A history whose ONLY user boundary would keep an orphan tool result is
/// folded to the digest alone rather than to a dangling pair.
#[test]
def test_a_history_with_no_usable_boundary_folds_to_the_digest : Bool :=
    let s : Session := session_with [tool_msg (big 4000i64)] in
    match Fold.fold_session s history_dir 1i64 200i64 {
        Option.none => false,
        Option.some out =>
            match out.session.history {
                List.cons m rest =>
                    Bool.and (match m.role { Role.system_ => true, _ => false }) (List.length rest == 0i64),
                List.empty => false,
            },
    }

/// The digest must not lose what the model needs to know a result existed:
/// each dropped tool result contributes its byte size.
#[test]
def test_digest_sizes_every_dropped_tool_result : Bool :=
    let out : String := big 4000i64 in
    let body : String := Fold.digest_body [user_msg "run it", tool_msg out] in
    String.contains body "4000"

#[test]
def test_digest_names_the_tool_a_call_used : Bool :=
    let call : Message := { role := Role.assistant, content := [Content.tool_use "call_1" "read_file" (JsonNull)] } in
    let body : String := Fold.digest_body [call] in
    String.contains body "read_file"

#[test]
def test_digest_keeps_the_first_line_of_a_long_text_block : Bool :=
    let body : String := Fold.digest_body [user_msg (String.concat "the ask\n" (big 4000i64))] in
    Bool.and (String.contains body "the ask") (Bool.not (String.contains body (big 100i64)))

/// The pointer names the session's own history directory and both read-tool
/// knobs, so the model can go and read the verbatim turns.
#[test]
def test_pointer_names_the_directory_and_the_read_knobs : Bool :=
    let p : String := Fold.pointer_line "/sessions/s-fold" 7i64 in
    Bool.and (String.contains p "/sessions/s-fold")
        (Bool.and (String.contains p "offset") (String.contains p "limit"))

/// The note the resume prints names the digest and the history directory;
/// a folded session is otherwise a normal session.
#[test]
def test_digest_note_names_the_directory : Bool :=
    let note : String := Fold.digest_note 42i64 "/sessions/s-fold" in
    Bool.and (String.contains note "42") (String.contains note "/sessions/s-fold")

/// The digest is a SYSTEM message: it is context, not a user turn.
#[test]
def test_the_digest_is_a_system_message : Bool :=
    let old : List Message := [user_msg (big 4000i64), assistant_msg (big 4000i64)] in
    let s : Session := session_with old in
    match Fold.fold_session s history_dir 1i64 200i64 {
        Option.none => false,
        Option.some out =>
            match out.session.history {
                List.cons m _ => match m.role { Role.system_ => true, _ => false },
                List.empty => false,
            },
    }

/// The outcome's numbers are the ones the one UI renderer prints: `before`
/// is the unfolded message count, `after` the folded one, `tokens` the new
/// estimate.
#[test]
def test_the_outcome_reports_the_message_counts : Bool :=
    let history : List Message := [user_msg (big 4000i64), assistant_msg (big 4000i64), user_msg "recent ask"] in
    let s : Session := session_with history in
    match Fold.fold_session s history_dir 1i64 5i64 {
        Option.none => false,
        Option.some out =>
            Bool.and (out.before == List.length history)
                (Bool.and (out.after == 2i64) (Bool.not (I64.lt out.tokens 0i64))),
    }

/// A zero budget disables the fold, the same way `context_window = 0`
/// disables autocompact: the knob has an off switch.
#[test]
def test_a_zero_budget_disables_the_fold : Bool :=
    let s : Session := session_with [user_msg (big 4000i64), assistant_msg (big 4000i64)] in
    match Fold.fold_session s history_dir 1i64 0i64 {
        Option.none => true,
        Option.some _ => false,
    }

/// Folding is idempotent in the observable sense: a folded session is under
/// its budget, so folding it again is a no-op (the second restart replays
/// only the fold).
#[test]
def test_a_folded_session_does_not_fold_again : Bool :=
    let old : List Message := [user_msg (big 4000i64), assistant_msg (big 4000i64)] in
    let s : Session := session_with old in
    match Fold.fold_session s history_dir 1i64 200i64 {
        Option.none => false,
        Option.some out => match Fold.fold_session out.session history_dir 1i64 200i64 {
            Option.none => true,
            Option.some _ => false,
        },
    }

/// The pointer must name the block the loaded history STARTS at, not a
/// constant: a session resumed after a compaction starts at
/// `history_base > 1`, and a pointer at block 1 would name a block the
/// resume never loaded (its messages are not in the model's context at all).
#[test]
def test_the_pointer_names_the_block_the_history_starts_at : Bool :=
    let old : List Message := [user_msg (big 4000i64), assistant_msg (big 4000i64)] in
    let s : Session := session_with old in
    match Fold.fold_session s history_dir 9i64 200i64 {
        Option.none => false,
        Option.some out => match out.session.history {
            List.cons m _ => match m.content {
                List.cons c _ => match c {
                    Content.text text => Bool.and (String.contains text "/history blocks, starting at 9.json")
                        (Bool.not (String.contains text "starting at 1.json")),
                    _ => false,
                },
                List.empty => false,
            },
            List.empty => false,
        },
    }

/// `JsonNull`: the tool_use input of a call whose arguments do not matter
/// to the digest.
def JsonNull : Json := Json.make_null
