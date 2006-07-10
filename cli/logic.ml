
open Datatype

let __strategy : Strategy.strategy option ref = ref None
let __matchpatt : (Type.bt -> string) option ref = ref None
let __inputparser : (string -> Type.bt list) option ref = ref None
let __printer : (Basictype.formula -> string) option ref = ref None
let __history_list : (string * Type.t * history_type) list option ref = ref None
let __pp : (Type.bt list -> Type.bt list) option ref = ref None
let __neg : (Type.bt list -> Type.bt list) option ref = ref None
let __exit : (Variable.store list -> string) option ref = ref None
let __options : (Arg.key * Arg.spec * Arg.doc) list option ref = ref None
let __use_cache : bool ref = ref false
