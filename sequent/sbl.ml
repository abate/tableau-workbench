
type sbl = Comptypes.mixlist Data.Substlist.t

let add (sbl : sbl) l =
  List.fold_left (
      fun s (k,v) ->
              try
                  begin
                      match Data.Substlist.find k s with
                      |`L(l) -> Data.Substlist.add k (`L(l#addlist v)) s
                      |`S(l) -> Data.Substlist.add k (`S(l#addlist v)) s
                      |#Comptypes.mixlist -> failwith "add type node allowed"
                  end
              with Not_found ->  (
                  Data.Substlist.add k (`L((new Comptypes.Mtlist.listobj)#addlist v)) s )
      ) sbl l

let mem sbl p f =
    try
        match Data.Substlist.find p sbl with
        |`L(l) -> l#mem f
        |#Comptypes.mixlist -> failwith "add type node allowed"
    with Not_found -> raise Not_found

(* XXX: FINISH ME *)
let to_string sbl =
    Data.Substlist.iter ( fun k e ->
        print_endline k ;
        print_endline (Comptypes.string_of_mixlist e)
    ) sbl
;;

