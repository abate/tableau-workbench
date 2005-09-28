
open Datatype

let __test : int ref = ref 0
let __strategy : Strategy.strategy option ref = ref None
let __matchpatt : (Type.bt -> string) option ref = ref None
let __inputparser : (string -> Type.bt list) option ref = ref None
let __history_list : (string * Type.t) list option ref = ref None
let __pp : (Type.bt list -> Type.bt list) option ref = ref None
let __neg : (Type.bt list -> Type.bt list) option ref = ref None

