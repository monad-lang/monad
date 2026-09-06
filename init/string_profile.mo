
use std.bench {now, report, since}

// ── Bridge overhead ──

#[test]
def profile_to_list : IO Bool := do {
	let long := String.repeat "x" 100;
	let start : I64 <- Bench.now;
	let ignored2 := String.to_list long;
	let elapsed : I64 <- Bench.since start;
	Bench.report "to_list (100 bytes)" elapsed;
	return true
}

#[test]
def profile_from_list : IO Bool := do {
	let bytes := String.to_list (String.repeat "x" 100);
	let start : I64 <- Bench.now;
	let ignored2 := String.from_list bytes;
	let elapsed : I64 <- Bench.since start;
	Bench.report "from_list (100 bytes)" elapsed;
	return true
}

// ── Native concat ──

#[test]
def profile_concat_native : IO Bool := do {
	let a := String.repeat "hello" 20;
	let b := String.repeat "world" 20;
	let start : I64 <- Bench.now;
	let ignored2 := String.concat a b;
	let elapsed : I64 <- Bench.since start;
	Bench.report "concat native (100+100 bytes)" elapsed;
	return true
}

// ── Length ──

#[test]
def profile_length_native : IO Bool := do {
	let long := String.repeat "x" 100;
	let start : I64 <- Bench.now;
	let ignored2 := String.length long;
	let elapsed : I64 <- Bench.since start;
	Bench.report "length native (100 bytes)" elapsed;
	return true
}

// ── Contains ──

#[test]
def profile_contains_short : IO Bool := do {
	let haystack := String.repeat "abcde" 20;
	let start : I64 <- Bench.now;
	let result := String.contains haystack "cde";
	let elapsed : I64 <- Bench.since start;
	Bench.report "contains (100 bytes, short needle)" elapsed;
	return true
}

#[test]
def profile_contains_miss : IO Bool := do {
	let haystack := String.repeat "abcde" 20;
	let start : I64 <- Bench.now;
	let result := String.contains haystack "xyz";
	let elapsed : I64 <- Bench.since start;
	Bench.report "contains miss (100 bytes)" elapsed;
	return true
}

// ── Reverse ──

#[test]
def profile_reverse : IO Bool := do {
	let long := String.repeat "hello " 20;
	let start : I64 <- Bench.now;
	let result := String.reverse long;
	let elapsed : I64 <- Bench.since start;
	Bench.report "reverse (120 bytes)" elapsed;
	return true
}

// ── Trim ──

#[test]
def profile_trim : IO Bool := do {
	let body := String.repeat "x" 50;
	let padded := String.concat "  " (String.concat body "  ");
	let start : I64 <- Bench.now;
	let result := String.trim padded;
	let elapsed : I64 <- Bench.since start;
	Bench.report "trim (50 bytes with padding)" elapsed;
	return true
}

// ── Repeat ──

#[test]
def profile_repeat_10 : IO Bool := do {
	let start : I64 <- Bench.now;
	let ignored2 := String.repeat "hello" 10;
	let elapsed : I64 <- Bench.since start;
	Bench.report "repeat 10x" elapsed;
	return true
}

// ── starts_with ──

#[test]
def profile_starts_with_true : IO Bool := do {
	let long := String.repeat "hello " 20;
	let start : I64 <- Bench.now;
	let result := String.starts_with long "hello";
	let elapsed : I64 <- Bench.since start;
	Bench.report "starts_with true (120 bytes)" elapsed;
	return true
}

#[test]
def profile_starts_with_false : IO Bool := do {
	let long := String.repeat "hello " 20;
	let start : I64 <- Bench.now;
	let result := String.starts_with long "world";
	let elapsed : I64 <- Bench.since start;
	Bench.report "starts_with false (120 bytes)" elapsed;
	return true
}
