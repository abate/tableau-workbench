(** this module return the the rule to apply and a new context *)

exception NoMoreRules

module type S =
    sig
        type rule
        type node
        type state
        type context
        type s = |S |SS of rule |R of rule |E 
        class strategy :
          string ->
          object
            val automata : (string, s * string * string) Hashtbl.t
            val start : state
            method add : string -> s -> string -> string -> unit
            method next : state -> node -> rule * context * state
            method start : state
          end
(*        type s = |S |SS of rule |R of rule |E 
        class type strategy =
            object
            method next : state -> node -> rule * context * state
            method add  : string -> s -> string -> string -> unit
            end
    *)
    end
 
module Make (R:Rule.S) 
(* 
:    sig
        type rule = R.rule
        type node = R.node
        type context = R.context
        type state
        exception NoMoreRules
        type s = |S |SS of rule |R of rule |E 
        class type strategy =
            object
            method next : state -> node -> rule * context * state
            method add  : string -> s -> string -> string -> unit
            end
      end 
*)
= struct

    module Map = Map.Make (
        struct
            type t = string
            let compare = compare
        end
    )

    (*exception NoMoreRules *)

    type rule = R.rule
    type node = R.node
    type context = R.context
    type state = { id : string; context : int Map.t }
    
    type input = Succ | Failed;;
    type s =
        |S          (* star *)
        |SS of rule (* single state star *)
        |R  of rule (* rule *)
        |E          (* exit *)

    type t = (id_t, val_t) Hashtbl.t
    and id_t = string
    and val_t = (s * string * string)
    
    (* add an element to the fsa *)
    let add automata id t n1 n2 = Hashtbl.add automata id (t,n1,n2)

    (* create a fresh state initialized to v *)
    let newstate id = { id = id ; context = Map.empty }
        
    (* return a new state / context *)
    let nextcxt n ?(v=0) = function
    |Some({id = i ; context = g}) -> { id = n ; context = Map.add i v g }
    |None -> { id = n ; context = Map.empty }

    (* check if the context associated to the state is equal to v *)
    let check v state =
            try (Map.find state.id state.context) = v
            with Not_found -> true

    (* given a state returns the next state. On success, reset the
     * state context. *)
    let rec seq automata inp state next =
      match inp with
      |Succ -> move automata inp (nextcxt next None)
      |Failed -> move automata inp (nextcxt next (Some(state)))

    (* given a state returns the same state and resets the
     * state context. On Failure, depending upon the state
     * context return the same state or move the next state *)
    and star automata inp state back out =
      match inp with
      |Succ -> move automata inp (nextcxt back None)
      |Failed when (check 0 state) ->
              move automata inp (nextcxt back ~v:1 (Some(state)))
      |Failed when (check 1 state) ->
              move automata inp (nextcxt out ~v:1 (Some(state)))
      |_ -> failwith "star"

    (* given a state returns the same state on success and
     * resets the state context or move to the next state on 
     * failure *)
    and singlestar automata inp state back out =
      match inp with
      |Succ -> move automata inp (nextcxt back None)
      |Failed -> move automata inp (nextcxt out ~v:1 (Some(state)))

    (* given a state makes a many move as possible 
     * to the next (non star) state *)
    and move automata inp state =
            try begin
                match Hashtbl.find automata state.id with
                |(S,back,out) ->
                        move automata inp (star automata inp state back out)
                |(SS(_),_,_) -> state
                |(R(_),_,_) -> state
                |(E,_,_) -> state
            end with Not_found -> failwith "strategy : move"

    (* make a transition in the fs from (non star) 
     * state to (non star) state *)
    let rec next automata state node =
            try begin
                match Hashtbl.find automata state.id with
                |(R(r),_,n) ->
                        let c = r#check node in
                        if c#is_valid then (r,c,seq automata Succ state n)
                        else (* the rule failed, we try the next one *)
                            next automata
                            (seq automata Failed state n)
                            node
                |(SS(r),back,out) -> 
                        let c = r#check node in
                        if c#is_valid then
                            (r,c,singlestar automata Succ state back out)
                        else (* the rule failed, we try the next one *)
                            next automata
                            (singlestar automata Failed state back out)
                            node
                |(S,_,_) -> failwith "strategy : step (S)"
                |(E,_,_) -> raise NoMoreRules
            end with Not_found -> failwith "strategy : step (not found)"

    class strategy start =
        object
        val automata = Hashtbl.create 20
        val start = newstate start
        method start = start
        method add id t n1 n2 = add automata id t n1 n2
        method next state node = next automata state node
        end
        
    end

