
open Datatype

let trace = ref false;;

let print (node : Node.node) name parentid childid =
    if !trace then
        begin
            let (m,h,_) = node#get in
            Printf.printf
            "%s ( %d -> %d )\n%s\n%s\n\n"
            name parentid childid
            (Store.to_string m)
            (History.to_string h)
        end
    else ()
;;

