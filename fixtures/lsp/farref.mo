// The cross-file navigation vector: a type, a constructor and a class this file uses
// and the prelude declares, so definition on each opens `init/src/prelude.mo` at the
// declaration. Positions are pinned by line in `session.jsonl`; keep this comment's
// line count.

def zz_replay_far_type : Option I64 := Option.none

def zz_replay_far_class [Add A] (x : A) : A := x

def zz_replay_far_ctor : Option I64 := none
