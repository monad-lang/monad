
use std.test
use std.bench

// ── Bridge overhead ──

@[test]
def profile_to_list : Bool :=
	let long := String.repeat "x" 100 in
	let start := Bench.now in
	let ignored2 := String.to_list long in
	let elapsed := I64.sub Bench.now start in
	Bench.report "to_list (100 bytes)" elapsed

@[test]
def profile_from_list : Bool :=
	let bytes := String.to_list (String.repeat "x" 100) in
	let start := Bench.now in
	let ignored2 := String.from_list bytes in
	let elapsed := I64.sub Bench.now start in
	Bench.report "from_list (100 bytes)" elapsed

// ── Native concat ──

@[test]
def profile_concat_native : Bool :=
	let a := String.repeat "hello" 20 in
	let b := String.repeat "world" 20 in
	let start := Bench.now in
	let ignored2 := String.concat a b in
	let elapsed := I64.sub Bench.now start in
	Bench.report "concat native (100+100 bytes)" elapsed

// ── Length ──

@[test]
def profile_length_native : Bool :=
	let long := String.repeat "x" 100 in
	let start := Bench.now in
	let ignored2 := String.length long in
	let elapsed := I64.sub Bench.now start in
	Bench.report "length native (100 bytes)" elapsed

// ── Contains ──

@[test]
def profile_contains_short : Bool :=
	let haystack := String.repeat "abcde" 20 in
	let start := Bench.now in
	let result := String.contains haystack "cde" in
	let elapsed := I64.sub Bench.now start in
	Bench.report "contains (100 bytes, short needle)" elapsed

@[test]
def profile_contains_miss : Bool :=
	let haystack := String.repeat "abcde" 20 in
	let start := Bench.now in
	let result := String.contains haystack "xyz" in
	let elapsed := I64.sub Bench.now start in
	Bench.report "contains miss (100 bytes)" elapsed

// ── Reverse ──

@[test]
def profile_reverse : Bool :=
	let long := String.repeat "hello " 20 in
	let start := Bench.now in
	let result := String.reverse long in
	let elapsed := I64.sub Bench.now start in
	Bench.report "reverse (120 bytes)" elapsed

// ── Trim ──

@[test]
def profile_trim : Bool :=
	let body := String.repeat "x" 50 in
	let padded := String.concat "  " (String.concat body "  ") in
	let start := Bench.now in
	let result := String.trim padded in
	let elapsed := I64.sub Bench.now start in
	Bench.report "trim (50 bytes with padding)" elapsed

// ── Repeat ──

@[test]
def profile_repeat_10 : Bool :=
	let start := Bench.now in
	let ignored2 := String.repeat "hello" 10 in
	let elapsed := I64.sub Bench.now start in
	Bench.report "repeat 10x" elapsed

// ── starts_with ──

@[test]
def profile_starts_with_true : Bool :=
	let long := String.repeat "hello " 20 in
	let start := Bench.now in
	let result := String.starts_with long "hello" in
	let elapsed := I64.sub Bench.now start in
	Bench.report "starts_with true (120 bytes)" elapsed

@[test]
def profile_starts_with_false : Bool :=
	let long := String.repeat "hello " 20 in
	let start := Bench.now in
	let result := String.starts_with long "world" in
	let elapsed := I64.sub Bench.now start in
	Bench.report "starts_with false (120 bytes)" elapsed
