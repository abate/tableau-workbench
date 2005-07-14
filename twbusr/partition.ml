

module Make(P: NodePattern.S)(H: NodePattern.S) :
    sig
        val match_node :
            (P.bt, P.bt Sets.st) Gmap.mt ->
                 P.pattern list * P.pattern list * P.pattern list ->
                    P.sbl Enum.t

        val match_hist : H.sbl Enum.t -> H.bt Hmap.mt -> H.pattern list -> H.sbl

        exception FailedMatch
    end 
= struct
        open ExtLib    
        module Substlist = Data.Substlist

        exception FailedMatch

        let check (sbl,htbl) pmatch f =
            if not(Hashtbl.mem htbl f) then
                try
                    let s = pmatch sbl [f] in
                    let _ = Hashtbl.add htbl f () in
                    Some(s,htbl)
                with FailedMatch -> None
            else None
            
        (* XXX: since I'm using an hash table, I risk a key  collision *)
        let init () = (Substlist.empty, Hashtbl.create 7)
        
        let enum store patternlist =
            let rec enum_aux = function
                |[] -> Enum.empty ()
                |patt::[] ->
                        let el = (store#get patt.P.pid)#elements in
                        Enum.filter_map (fun x ->
                            check (init ()) patt.P.pmatch x
                        ) (List.enum el)
                |patt::pl ->
                        let el = (store#get patt.P.pid)#elements in
                        Enum.concat (
                            Enum.map (fun x ->
                                Enum.filter_map (
                                    fun tbl ->
                                        check tbl patt.P.pmatch x
                                ) (Enum.clone (enum_aux pl))
                            ) (List.enum el)
                        )
            in enum_aux patternlist

        (* we get all formulae associated with a patter minus the
         * formulae that have been selected to be proncipal formulae.
         *  
         * FIXME: This could faster. I know that a formula might be 
         * in the htbl only is the patt is similar to the pattern of 
         * the principal formulae
         *)
        let getset store subsl htbl patt =
            let s = store#get patt.P.pid in
            let l = List.filter(
                fun f -> not(Hashtbl.mem htbl f)
            ) s#elements
            in patt.P.pmatch subsl l
        ;;
            
        (* Return an enumeration with all possible nodes *)
        let match_node store (pl,sl,ll) = 
                try
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
        ;;

        let rec match_hist enum store hl =
            try
                begin
                    match Enum.get enum with
                    |Some(sbl) ->
                            List.fold_left (
                                fun s p -> p.H.pmatch s [(store#get p.H.pid)]
                            ) sbl hl
                    |None -> Substlist.empty
                end 
            with FailedMatch -> match_hist enum store hl
           
    end
