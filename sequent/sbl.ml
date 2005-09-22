
type sbl = Comptypes.mixlist Data.Substlist.t

let add (sbl : sbl) l =
  List.fold_left (
      fun s (k,v) ->
              try
                  begin
                      match Data.Substlist.find k s with
                      |`Mtlist(l) -> Data.Substlist.add k (`Mtlist(l#addlist v)) s
                      |`Set(l) -> Data.Substlist.add k (`Set(l#addlist v)) s
                      |#Comptypes.mixlist -> failwith "add type node allowed"
                  end
              with Not_found ->  (
                  Data.Substlist.add k (`Mtlist((new Comptypes.Mtlist.listobj)#addlist v)) s )
      ) sbl l

let mem sbl p f =
    try
        match Data.Substlist.find p sbl with
        |`Mtlist(l) -> l#mem f
        |#Comptypes.mixlist -> failwith "add type node allowed"
    with Not_found -> raise Not_found

(* XXX: FINISH ME *)
let to_string sbl =
    Data.Substlist.iter ( fun k e ->
        print_endline k ;
        print_endline (Comptypes.string_of_mixlist e)
    ) sbl
;;

