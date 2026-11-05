/// `site.toml` parsing.
use lib::config {SiteConfig, SiteConfig.parse, SiteConfig.with_out}

def parsed_or_default (src : String) : SiteConfig :=
    match SiteConfig.parse src {
        Result.ok c => c,
        Result.err _ => { title := "ERR", base_url := "", book_src := "", book_dir := "", out_dir := "" },
    }

#[test]
def test_defaults_when_empty : Bool :=
    let c : SiteConfig := parsed_or_default "" in
    String.beq c.book_src "docs/src" && String.beq c.book_dir "docs" && String.beq c.out_dir "docs/public"

#[test]
def test_reads_keys : Bool :=
    let c : SiteConfig := parsed_or_default "title = \"T\"\nout = \"x\"\n[book]\nsrc = \"b\"\n" in
    String.beq c.title "T" && String.beq c.out_dir "x" && String.beq c.book_src "b"

#[test]
def test_wrong_type_is_error : Bool :=
    match SiteConfig.parse "title = 3\n" {
        Result.err _ => true,
        Result.ok _ => false,
    }

#[test]
def test_out_override : Bool :=
    let c : SiteConfig := SiteConfig.with_out (Option.some "y") (parsed_or_default "") in
    String.beq c.out_dir "y"
