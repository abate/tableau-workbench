
class type ['t,'bt] st =
    object('sub)
        method add : (string * 'bt list) list -> 'sub
        method find : string -> 't
        method is_empty : bool
        method mem : string -> 'bt -> bool
        method copy : 'sub
        method empty : 'sub
        method to_string : string
      end

module Make : 
    sig
        class substitution : [Comptypes.mixlist, Basictype.mixtype] st
    end
    = struct
        
    module Sbl = Map.Make(
        struct
            type t = string
            let compare = Pervasives.compare
        end)

    exception Stop
    
    class substitution =
        object
            val sbl = Sbl.empty
            
            method add l =
                let sbl' =
                    List.fold_left (
                        fun s (k,v) ->
                            try begin
                                match Sbl.find k s with
                                |`List(l) -> Sbl.add k (`List(l#addlist v)) s
                                |`Set(l) -> Sbl.add k (`Set(l#addlist v)) s
                                |#Comptypes.mixlist -> failwith "Sbl.add : type node allowed"
                                end
                            with Not_found -> (
                                Sbl.add k (
                                    `List((new Comptypes.Mtlist.listobj)#addlist v)
                                    ) s 
                                )
                    ) sbl l
                in {< sbl = sbl' >}

            (* XXX: this method could return the container ... *)
            method find k = Sbl.find k sbl
            
            method mem p f =
                try
                    match Sbl.find p sbl with
                    |`List(l) -> l#mem f
                    |#Comptypes.mixlist -> failwith "Sbl.mem : type node allowed"
                with Not_found -> raise Not_found

            method is_empty = 
                try
                    Sbl.fold (fun _ v b ->
                        match v,b with
                        |`List(l),true -> l#is_empty 
                        |`Set(l),true -> l#is_empty
                        |`List(l),false -> raise Stop
                        |`Set(l),false -> raise Stop
                        |#Comptypes.mixlist,_ -> failwith "Sbl.is_empty : type node allowed"
                    ) sbl true
                with Stop -> false
                
            method copy = {< >}

            method empty = 
                let sbl' = 
                    Sbl.map (function
                        |`List(l) -> `List(l#empty)
                        |`Set(l) -> `Set(l#empty)
                        |#Comptypes.mixlist -> failwith "Sbl.is_empty : type node allowed"
                    ) sbl
                in {< sbl = sbl' >}

            (* XXX: FINISH ME *)
            method to_string = 
                Sbl.fold ( fun k e s ->
                    Printf.sprintf "%skey:%s = %s\n" s k (Comptypes.string_of_mixlist e)
                ) sbl ""
        end
    end
