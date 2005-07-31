(** this module return the the rule to apply and a new context *)

module type S =
    sig
        type rule
        type node
        type state
        type context
        exception NoMoreRules
        val next : state -> node -> rule * context * state
    end
 
module Make (R:Rule.S)
(* :
    sig
        type rule = R.rule
        type node = R.node
        type context = R.context
        type state
        exception NoMoreRules
        val next : state -> node -> rule * context * state
    end 
*)
= struct

    module Map = Map.Make (
        struct
            type t = string
            let compare = compare
        end
    )

    exception NoMoreRules

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

    (* the fsa *)
    let automata = Hashtbl.create 15

    (* add an element to the fsa *)
    let add id t n1 n2 = Hashtbl.add automata id (t,n1,n2)

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
    let rec seq inp state local next =
      match inp with
      |Succ -> move inp (nextcxt next None)
      |Failed -> move inp (nextcxt next (Some(state)))

    (* given a state returns the same state and resets the
     * state context. On Failure, depending upon the state
     * context return the same state or move the next state *)
    and star inp state back out =
      match inp with
      |Succ -> move inp (nextcxt back None)
      |Failed when (check 0 state) -> move inp (nextcxt back ~v:1 (Some(state)))
      |Failed when (check 1 state) -> move inp (nextcxt out ~v:1 (Some(state)))
      |_ -> failwith "star"

    (* given a state returns the same state on success and
     * resets the state context or move to the next state on 
     * failure *)
    and singlestar inp state back out =
      match inp with
      |Succ -> move inp (nextcxt back None)
      |Failed -> move inp (nextcxt out ~v:1 (Some(state)))

    (* given a state makes a many move as possible 
     * to the next (non star) state *)
    and move inp state =
            try begin
                match Hashtbl.find automata state.id with
                |(S,n1,n2) -> move inp (star inp state n1 n2)
                |(SS(_),_,_) -> state
                |(R(_),_,_) -> state
                |(E,_,_) -> state
            end with Not_found -> failwith "strategy : move"

    (* make a transition in the fs from (non star) 
     * state to (non star) state *)
    let rec next state node =
            try begin
                match Hashtbl.find automata state.id with
                |(R(r),n1,n2) ->
                        let c = r#check node in
                        if c#is_valid then (r,c,seq Succ state n1 n2)
                        else (* the rule failed, we try the next one *)
                            next (seq Failed state n1 n2) node
                |(SS(r),n1,n2) -> 
                        let c = r#check node in
                        if c#is_valid then (r,c,singlestar Succ state n1 n2)
                        else (* the rule failed, we try the next one *)
                            next (singlestar Failed state n1 n2) node
                |(S,_,_) -> failwith "strategy : step"
                |(E,_,_) -> raise NoMoreRules
            end with Not_found -> failwith "strategy : step"

    end

