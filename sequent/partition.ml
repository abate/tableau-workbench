
module type S =
    sig
    type t
    type map (* map type *)
    type pt (* node pattern type *)
    type sbl
    type enum = (sbl * map) Enum.t
    val match_node : map -> (pt * pt) -> enum
    exception FailedMatch
    end 
;;

module Make(P: NodePattern.S) =
    struct

    type t = P.t
    type map = P.map
    type pt = P.pattern list
    type sbl = P.sbl
    type context = (sbl * map)
    type enum = context Enum.t
    exception FailedMatch

    open ExtLib    
    
    (* run the pmatch function and remove the formula from
     * the store if it matches *)
    let check ((sbl,store) : context) pmatch f =
            try
                let s = pmatch sbl [f] in
                let newstore = store#del f in
                Some(s,newstore)
            with FailedMatch -> None
        
    let init (sbl,store) = (sbl#copy, store#copy)
    
    let enum store patternlist =
        let rec enum_aux (newsbl,newstore) = function
            |[] -> Enum.empty ()
            |patt::[] ->
                    let el = (newstore#get patt.P.pid)#elements in
                    Enum.filter_map (fun x ->
                        check (init (newsbl,newstore)) patt.P.pmatch x
                    ) (List.enum el)
            |patt::pl ->
                    let el = (newstore#get patt.P.pid)#elements in
                    Enum.concat (
                        Enum.map (fun x ->
                            Enum.filter_map (
                                fun tbl ->
                                    check tbl patt.P.pmatch x
                            ) (Enum.clone (enum_aux (newsbl,newstore#copy) pl))
                        ) (List.enum el)
                    )
        in enum_aux store patternlist

    (* we get all formulae associated with a patter minus the
     * formulae that have been selected to be principal formulae.
     *  
     * XXX: This could faster. I know that a formula might be 
     * in the htbl only is the patt is similar to the pattern of 
     * the principal formulae
     *)
    let getset store pattlist =
        List.fold_left (
            fun (subl,ns) patt ->
                let s = ns#get patt.P.pid in
                let l = s#elements in
                let sbl' = patt.P.pmatch subl l in
                (sbl',List.fold_left (fun st e -> st#del e ) ns l)
        ) store pattlist
    ;;
    
    let removepl store pattlist =
        List.fold_left (
            fun (subl,ns) patt ->
                let s = ns#get patt.P.pid in
                match s#elements with
                |[] -> (patt.P.pmatch subl [],ns)
                |l ->
                    List.fold_left (fun (in_s,in_m) e ->
                        match check (in_s,in_m) patt.P.pmatch e with
                        |Some(res_s,res_m) -> (res_s,res_m)
                        |None -> (in_s,in_m)
                    ) (subl,ns) l
        ) (init store) pattlist
    ;;

    (* Return an enumeration with all possible nodes *)
    let match_node_one map (pl,sl) = 
            try (Enum.map (fun s -> getset s sl) (enum map pl))
            with FailedMatch -> Enum.empty ()
    ;;

    (* Return an enumeration with all possible nodes *)
    let match_node_zero map (pl,sl) = 
            try 
                let he = enum map pl in
                if Enum.is_empty he && not (sl = []) then
                        (Enum.init 1 (fun _ ->
                            let (newsbl, newmap) = removepl map pl in
                            getset (newsbl#empty,newmap) sl
                            ) 
                        )
                else (Enum.map (fun s -> getset s sl) he)
            with FailedMatch -> Enum.empty ()
    ;;

    (* Return an enumeration that contains only the
     * set of the side/set pattern *)
    let match_node_set map sl =
        try (Enum.init 1 (fun _ -> getset map sl ))
        with FailedMatch -> Enum.empty ()
    ;;
    
    (* Return an enumeration with all possible nodes 
     * but also attach one enumeration of the set of
     * the side/set patterns minus the principal 
     * formulae *)
    let match_node_trail map (plzero,plone,sl) = 
            try
                let pl = plone@plzero in
                let all_enum =
                    (Enum.map (fun s -> getset s sl) (enum map pl))
                in
                let trail_enum = 
                    (Enum.init 1 (fun _ ->
                        let (newsbl, newmap) = removepl map pl in
                        getset (newsbl#empty,newmap) sl
                        ) 
                    )
                in
                if (pl = []) && not(sl = []) then trail_enum
                else if Enum.is_empty all_enum then 
                    (if sl = [] then Enum.empty ()
                    else trail_enum)
                else
                    (if sl = [] then all_enum
                     else Enum.append all_enum trail_enum)
            with FailedMatch -> Enum.empty ()
    ;;

end
