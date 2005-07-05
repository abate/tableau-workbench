
module Make(P: NodePattern.S) = struct
    open P

    let build_node node sbl nodeaction = function
        { aname = name ; action = al } ->
            match node#get name with
            |`FMap(store) ->
                let newstore =
                    List.fold_left (fun s a ->
                        s#addlist ~id:a.aid (a.paction sbl)
                    ) store al
                in node#set name (`FMap(newstore))
            |#Comptypes.mixlist -> failwith "build_node"
end
