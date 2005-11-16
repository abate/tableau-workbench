(** this module return the the rule to apply and a new context *)

module Make (R:Rule.S) = struct

    module Map = Map.Make (
        struct
            type t = string
            let compare = compare
        end
    )

    type rule = R.rule
    type node = R.node
    type context = R.context
    type state = { id : string; alt : string; context : int Map.t }
    
    type input = Succ | Failed;;
    type s =
        |S          (* star *)
        |SS of rule (* single state star *)
        |R  of rule (* rule *)
        |E__          (* exit *)

    type t = (id_t, val_t) Hashtbl.t
    and id_t = string
    and val_t = (s * string * string * string * (node -> bool))
    
    (* add an element to the fsa *)
    let add automata id t n1 n2 n3 f = Hashtbl.add automata id (t,n1,n2,n3,f)

    (* return a new state / context *)
    let nextcxt n a ?(v=0) = function
        |Some({id = i ; context = g}) -> { id = n ; alt = a ; context = Map.add i v g }
        |None -> { id = n ; alt = a; context = Map.empty }

    (* check if the context associated to the state is equal to v *)
    let check v state =
            try (Map.find state.id state.context) = v
            with Not_found -> true

    (* given a state returns the next state. On success, reset the
     * state context. *)
    let rec seq automata inp state next alt =
      match inp with
      |Succ -> move automata inp (nextcxt next alt None)
      |Failed -> move automata inp (nextcxt next alt (Some(state)))

    (* given a state returns the same state and resets the
     * state context. On Failure, depending upon the state
     * context return the same state or move the next state *)
    and star automata inp state back out alt =
      match inp with
      |Succ -> move automata inp (nextcxt back alt None)
      |Failed when (check 0 state) ->
              move automata inp (nextcxt back alt ~v:1 (Some(state)))
      |Failed when (check 1 state) ->
              move automata inp (nextcxt out alt ~v:1 (Some(state)))
      |_ -> failwith "star"

    (* given a state returns the same state on success and
     * resets the state context or move to the next state on 
     * failure *)
    and singlestar automata inp state back out alt =
      match inp with
      |Succ -> move automata inp (nextcxt back alt None)
      |Failed -> move automata inp (nextcxt out alt ~v:1 (Some(state)))

    (* given a state makes a many move as possible 
     * to the next (non star) state *)
    and move automata inp state =
            try begin
                match Hashtbl.find automata state.id with
                |(S,back,out,_,_) ->
                        move automata inp
                        (star automata inp state back out state.alt)
                |_ -> state 
            end with Not_found -> failwith "strategy : move"

    exception NoAltRule
    
    let altstate automata state resnode =
        if state.alt = "" then raise NoAltRule
        else
        try begin
            match Hashtbl.find automata state.alt with
            |(R(_),_,_,alt,f) 
            |(SS(_),_,_,alt,f)
            |(S,_,_,alt,f)
            |(E__,_,_,alt,f) ->
                    if f (Option.get resnode)
                    then {state with id = state.alt ; alt = alt }
                    else raise NoAltRule
            end
        with Not_found -> failwith ("altstate "^state.alt)
        
    (* make a transition in the fs from (non star) 
     * state to (non star) state *)
    let rec next automata state resnode node =
        let newstate =
            try if Option.is_none resnode then { state with alt = "" }
            else altstate automata state resnode
            with NoAltRule -> raise Strategy.NoMoreRules
        in
        try begin
            match Hashtbl.find automata newstate.id with
            |(R(r),succ,fail,alt,_) ->
                    let c = r#check node in
                    if c#is_valid then 
                            (r,c,seq automata Succ newstate succ alt)
                    else (* the rule failed, we try the next one *)
                        next automata
                        (seq automata Failed newstate fail alt)
                        None
                        node
            |(SS(r),back,out,alt,_) -> 
                    let c = r#check node in
                    if c#is_valid then
                        (r,c,singlestar automata Succ newstate back out alt)
                    else (* the rule failed, we try the next one *)
                        next automata
                        (singlestar automata Failed newstate back out alt)
                        None
                        node
            |(S,_,_,_,_) -> failwith "strategy : step (S)"
            |(E__,_,_,_,_) -> raise Strategy.NoMoreRules
        end with Not_found -> failwith "strategy : step (not found)"

    class strategy start =
        object
        val automata = Hashtbl.create 20
        val start = { id = start ; alt = "" ; context = Map.empty }
        method start = start
        method add id ?alt ?cond t n1 n2 =
            let alt = if Option.is_none alt then "" else Option.get alt in
            let f   =
                if Option.is_none cond then (fun _ -> false)
                else Option.get cond
            in add automata id t n1 n2 alt f
        method next state (resnode: node option) node = next automata state resnode node
        end
        
end

