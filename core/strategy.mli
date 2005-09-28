exception NoMoreRules
module type S =
  sig
    type rule
    type node
    type state
    type context
    type s = S | SS of rule | R of rule | E
    class strategy :
      string ->
      object
        val automata : (string, s * string * string) Hashtbl.t
        val start : state
        method add : string -> s -> string -> string -> unit
        method next : state -> node -> rule * context * state
        method start : state
      end
  end
module Make :
  functor (R : Rule.S) ->
    sig
      module Map :
        sig
          type key = string
          type +'a t
          val empty : 'a t
          val is_empty : 'a t -> bool
          val add : key -> 'a -> 'a t -> 'a t
          val find : key -> 'a t -> 'a
          val remove : key -> 'a t -> 'a t
          val mem : key -> 'a t -> bool
          val iter : (key -> 'a -> unit) -> 'a t -> unit
          val map : ('a -> 'b) -> 'a t -> 'b t
          val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
          val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
          val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
          val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
        end
      type rule = R.rule
      type node = R.node
      type context = R.context
      type state = { id : string; context : int Map.t; }
      type input = Succ | Failed
      type s = S | SS of rule | R of rule | E
      type t = (id_t, val_t) Hashtbl.t
      and id_t = string
      and val_t = s * string * string
      val add : ('a, 'b * 'c * 'd) Hashtbl.t -> 'a -> 'b -> 'c -> 'd -> unit
      val newstate : string -> state
      val nextcxt : string -> ?v:int -> state option -> state
      val check : int -> state -> bool
      val seq :
        (string, s * string * string) Hashtbl.t ->
        input -> state -> string -> state
      val star :
        (string, s * string * string) Hashtbl.t ->
        input -> state -> string -> string -> state
      val singlestar :
        (string, s * string * string) Hashtbl.t ->
        input -> state -> string -> string -> state
      val move :
        (string, s * string * string) Hashtbl.t -> input -> state -> state
      val next :
        (string, s * string * string) Hashtbl.t ->
        state -> R.node -> rule * R.context * state
      class strategy :
        string ->
        object
          val automata : (string, s * string * string) Hashtbl.t
          val start : state
          method add : string -> s -> string -> string -> unit
          method next : state -> R.node -> rule * R.context * state
          method start : state
        end
    end
