

module Make(P: NodePattern.S) =
    struct
        open P
        open ExtLib    
        module Substlist = Data.Substlist

        exception NodeFailedMatch
        exception FailedMatch

        let check (sbl,htbl) pmatch f =
            if not(Hashtbl.mem htbl f) then
                let s = pmatch sbl [f] in
                let _ = Hashtbl.add htbl f () in
                Some(s,htbl)
            else None
            
        (* XXX: since I'm using an hash table, I risk a key  collision *)
        let init () = (Substlist.empty, Hashtbl.create 7)
        
        let enum store patternlist =
            let rec enum_aux = function
                |[] -> Enum.empty ()
                |patt::[] ->
                        let el = store#get patt.pid in
                        Enum.filter_map (fun x ->
                            check (init ()) patt.pmatch x
                        ) (List.enum el)
                |patt::pl ->
                        let el = store#get patt.pid in
                        Enum.concat (
                            Enum.map (fun x ->
                                Enum.filter_map (
                                    fun tbl ->
                                        check tbl patt.pmatch x
                                ) (Enum.clone (enum_aux pl))
                            ) (List.enum el)
                        )
            in enum_aux patternlist

        (* we get all formulae associated with a patter minus the
         * formulae that have been selected to be proncipal formulae.
         *  
         * FIXME: This could faster. I know that a formula might be 
         * in the htbl only is the patt is simular to the pattern of 
         * the principal formulae
         *)
        let getset store subsl htbl patt =
            let fl =
                List.filter (
                    fun f -> not(Hashtbl.mem htbl f)
                ) (store#get patt.pid)
            in patt.pmatch subsl fl

        (* Return an enumeration with all possible nodes *)
        let match_node node = function
            { pname = name ; chained = pl ; strict = sl; loose = ll } ->
            match node#get name with
            |`FMap(store) ->
                begin try
                    Enum.map (
                        fun (subsl,htbl) ->
                                    let tmpsl =
                                        List.fold_left (
                                            fun subl patt ->
                                                getset store subl htbl patt
                                        ) subsl sl
                                    in
                                    List.fold_left (
                                        fun subl patt ->
                                                getset store subl htbl patt
                                    ) tmpsl ll
                    ) (enum store pl)
                with FailedMatch -> Enum.empty ()
                end
            |#Comptypes.mixlist -> failwith "ooo"

    end
