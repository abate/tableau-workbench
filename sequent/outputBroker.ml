
open Datatype

let print (node : Node.node) name parentid childid =
    Printf.printf "%s ( %d -> %d )\n" name parentid childid;
    print_endline (node#to_string);
    print_newline ()
;;

