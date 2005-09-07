

module Make(P: NodePattern.S)(H: NodePattern.S) :
    sig
    val match_node : (P.bt, P.bt Sets.st) Gmap.mt ->
        P.pattern list * P.pattern list * P.pattern list ->
            (P.sbl * (P.bt, P.bt Sets.st) Gmap.mt) Enum.t

    val match_hist : (H.sbl * (P.bt, P.bt Sets.st) Gmap.mt) Enum.t -> 
        H.bt Hmap.mt -> (P.bt, P.bt Sets.st) Gmap.mt -> H.pattern list -> 
            (H.sbl * (P.bt, P.bt Sets.st) Gmap.mt)

    exception FailedMatch
    end 
= struct
        open ExtLib    
        module Substlist = Data.Substlist

        exception FailedMatch

        type context = (P.sbl * (P.bt, P.bt Sets.st) Gmap.mt)
        
        (* run the pmatch function and remove the formula from
         * the store if it matches *)
        let check ((sbl,store) : context) pmatch f =
                try
                    let s = pmatch sbl [f] in
                    let newstore = store#del f in
                    Some(s,newstore)
                with FailedMatch -> None
            
        (* XXX: since I'm using an hash table, I risk a key  collision *)
        let init s = (Substlist.empty, s#copy)
        
        let enum store patternlist =
            let rec enum_aux newstore = function
                |[] -> Enum.empty ()
                |patt::[] ->
                        let el = (newstore#get patt.P.pid)#elements in
                        Enum.filter_map (fun x ->
                            check (init newstore) patt.P.pmatch x
                        ) (List.enum el)
                |patt::pl ->
                        let el = (newstore#get patt.P.pid)#elements in
                        Enum.concat (
                            Enum.map (fun x ->
                                Enum.filter_map (
                                    fun tbl ->
                                        check tbl patt.P.pmatch x
                                ) (Enum.clone (enum_aux newstore#copy pl))
                            ) (List.enum el)
                        )
            in enum_aux store patternlist

        (* we get all formulae associated with a patter minus the
         * formulae that have been selected to be principal formulae.
         *  
         * FIXME: This could faster. I know that a formula might be 
         * in the htbl only is the patt is similar to the pattern of 
         * the principal formulae
         *)
        let getset store subsl patt =
            let s = store#get patt.P.pid in
            let l = s#elements in
            let sbl' = patt.P.pmatch subsl l in
            (* FIXME: here I should be able to remove only those
             * formulae that have been matched by pmatch.
             * EX. partition starred and not starred formulae *)
            (sbl',List.fold_left (fun st e -> st#del e ) store l)
        ;;
        (* Return an enumeration with all possible nodes *)
        let match_node map (pl,sl,ll) = 
                try
                    Enum.map (
                        fun s ->
                                    let tmpsl =
                                        List.fold_left (
                                            fun (subl,ns) patt ->
                                                getset ns subl patt
                                        ) s sl
                                    in
                                    List.fold_left (
                                        fun (subl,ns) patt ->
                                                getset ns subl patt
                                    ) tmpsl ll
                    ) (enum map#copy pl)
                with FailedMatch -> Enum.empty ()
        ;;
        
        let rec match_hist enum hist map hl =
            try
                begin
                    match Enum.get enum with
                    |Some(sbl,ns) ->
                            let newsbl = 
                                List.fold_left (
                                    fun s p ->
                                        p.H.pmatch s [(hist#get p.H.pid)]
                                ) sbl hl
                            in (newsbl,ns)
                    |None -> (Substlist.empty,map)
                end 
            with FailedMatch -> match_hist enum hist map hl
            
    end
