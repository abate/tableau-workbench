
open Datatype

let trace = ref false;;

let print (node : Node.node) name parentid childid =
    if !trace then
        begin
            Printf.printf "%s ( %d -> %d )\n" name parentid childid;
            print_endline (node#to_string);
            print_newline ()
        end
    else ()
;;

