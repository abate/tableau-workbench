
module type S =
    sig
    type t
    type map (* map type *)
    type at (* node pattern type *)
    type hist
    type sbl 
    val build_node : map -> sbl -> hist -> hist -> at -> map
    end
;;


module Make(P: NodePattern.S) =
    
    struct
    
    type t = P.t
    type map = P.map
    type at = P.action list
    type hist = P.hist
    type sbl = P.sbl
    
    let build_node map sbl hist var al =
                    List.fold_left (fun (m : map) a ->
                        m#addlist ~id:a.P.aid (a.P.paction sbl hist var)
                    ) map al
    
    end
