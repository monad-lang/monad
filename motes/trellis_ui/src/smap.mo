// String-keyed maps over `std::map`'s bucket helpers, keyed by
// `String.hash`/`String.beq` so no class dispatch is involved (the reason
// `llvm::strmap` exists; that mote is native-only).

use std::map {
    HashMap, HashMap.bucket_insert_str, HashMap.bucket_lookup_str,
    HashMap.bucket_of, HashMap.empty_buckets, HashMap.get_bucket,
    HashMap.set_bucket, map,
}

pub def Smap.empty {V : Type} : HashMap String V := HashMap.map HashMap.empty_buckets

pub def Smap.insert {V : Type} (key : String) (val : V) (m : HashMap String V) : HashMap String V :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            HashMap.map (HashMap.set_bucket buckets idx
                (HashMap.bucket_insert_str key val (HashMap.get_bucket buckets idx)))
    }

pub def Smap.get {V : Type} (key : String) (m : HashMap String V) : Option V :=
    match m {
        HashMap.map buckets =>
            HashMap.bucket_lookup_str key (HashMap.get_bucket buckets (HashMap.bucket_of (String.hash key)))
    }

pub def Smap.has {V : Type} (key : String) (m : HashMap String V) : Bool :=
    match Smap.get key m { Option.some _ => true, Option.none => false }

pub def Smap.get_i64 (key : String) (fallback : I64) (m : HashMap String I64) : I64 :=
    match Smap.get key m { Option.some v => v, Option.none => fallback }

pub def Smap.get_str (key : String) (fallback : String) (m : HashMap String String) : String :=
    match Smap.get key m { Option.some v => v, Option.none => fallback }
