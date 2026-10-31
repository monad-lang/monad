// mty / weaver / models -- the API-loaded model picker: /model opens it with
// the current name marked, Enter applies the selection (echo + banner), and
// Esc closes it. Ported from scripts/weaver-tui-repro/pty_repro_models.py.
use mty::spawn {Mty, Output}
use mty::check {Check.report}
use weaver::mty_support {run_gated, with_root, fixture_path, spawn, not_found, quit_cleanly}
use std::io {IO.println}

def saw_alt (o : Output) : Bool := Output.contains o "\u{1b}[?1049h"

def found (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def models_go (m : Mty) : IO Bool := do {
    let up <- Mty.wait_until m saw_alt 6000;
    let s0 <- Mty.wait_until m (fn (o : Output) => found o "mock/wv-not-mock") 6000;
    let a <- Check.report "S0 the start model is the one asked for" s0;
    Mty.send_text m "/model\n";
    let opened <- Mty.wait_until m (fn (o : Output) => found o "Select a model") 4000;
    let b <- Check.report "S1 /model opens the picker" opened;
    let o1 <- Mty.output m;
    let c <- Check.report "S1 the picker marks the current name"
        (found o1 "current: wv-not-mock");
    let d <- Check.report "S1 the API list is shown" (found o1 "   mock");
    let e <- Check.report "S1 nothing was selected yet" (not_found o1 "model: mock");
    Mty.send_text m "\r";
    let selected <- Mty.wait_until m (fn (o : Output) =>
        Bool.and (not_found o "Select a model") (found o "model: mock")) 4000;
    let f <- Check.report "S2 Enter closes the picker" selected;
    let o2 <- Mty.output m;
    let g <- Check.report "S2 the choice is echoed" (found o2 "model: mock");
    let h <- Check.report "S2 the banner shows the new model" (found o2 "mock/mock");
    Mty.send_text m "/model\n";
    let reopened <- Mty.wait_until m (fn (o : Output) => found o "Select a model") 4000;
    let i <- Check.report "S3 /model opens the picker" reopened;
    Mty.send_text m "\u{1b}";
    let closed <- Mty.wait_until m (fn (o : Output) => not_found o "Select a model") 4000;
    let j <- Check.report "S3 Esc closes the picker" closed;
    let restored <- quit_cleanly m 3000;
    let k <- Check.report "S4 quit restores the terminal" restored;
    Mty.finish m;
    return (up && a && b && c && d && e && f && g && h && i && j && k)
}

def models_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_slow.json";
    let r <- spawn bin "wv-not-mock" 20 80 root (Option.some turns) List.empty;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL mty models spawn: " e); return false },
        Result.ok m => models_go m
    }
}

#[test]
def test_model_picker_select_and_cancel : IO Bool :=
    run_gated "mty weaver models" test_models_body

def test_models_body (bin : String) : IO Bool :=
    with_root "models" (fn (root : String) => models_run bin root)
