
module Make(P: NodePattern.S) (*:
    sig
        val build_node : (P.bt, P.bt Sets.st) Gmap.mt -> P.sbl ->
            P.action list -> (P.bt, P.bt Sets.st) Gmap.mt
    end *)
= struct
    
    let build_node (map : (P.bt, P.bt Sets.st) Gmap.mt ) sbl hist al = 
                    List.fold_left (fun (m : (P.bt, P.bt Sets.st) Gmap.mt ) a ->
                        m#addlist ~id:a.P.aid (a.P.paction sbl hist)
                    ) map al 
end
