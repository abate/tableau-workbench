
open Unix
open Str
open Findlib


module Options = struct
    let verbose = ref false
    let tmp = ref "/tmp/"
end
;;

(* Findlib.init () ;; *)

let options = [
    ("-v",  Arg.Set Options.verbose, "verbose");
    ("-t",  Arg.String (fun s -> Options.tmp := s),  "temporary directory")
]
;;

let usage = "usage: compile [-options] [file.ml]" ;;

let input_file = ref None;;
let file f =
    try
        match f with
        |s when Str.string_match (Str.regexp "^[\n\t ]*$") s 0 -> ()
        |_ -> input_file := Some(f)
    with _ -> () 
;;

let get = function
    |None -> failwith "no input file"
    |Some v -> v
;;

let print_verbose fmt_etc =
    let print s = 
        if (!Options.verbose) then (
            Printf.printf "%s" s;
            Pervasives.flush Pervasives.stdout
        )
        else (
            print_string ".";
            Pervasives.flush Pervasives.stdout
        ) 
    in
    Printf.ksprintf print fmt_etc
;;

let str_lib_loc =
    try Findlib.package_directory "str"
    with No_such_package (p,i) -> failwith p^i
;;

let ext_lib_loc =
    try Findlib.package_directory "extlib"
    with No_such_package (p,i) -> failwith p^i
;;

let twb_lib_loc =
    try Findlib.package_directory "twb"
    with No_such_package (p,i) -> failwith p^i
;;

let noext filename =
    if Str.string_match (Str.regexp "^\\(.*\\).ml$") filename 0 then
        Str.matched_group 1 filename
    else
        filename
;;
  
let read_lines fc =
    let read_new_line n = 
        try Some (input_line fc)
        with End_of_file -> None
    in
        Stream.from read_new_line
;;

(* pre-processing *)
let pp filename = 
   print_verbose "pre-processing: %s\n" filename;
   let cmd = 
       "camlp4o "^
       str_lib_loc ^ "/str.cma "^
       ext_lib_loc ^ "/extLib.cma "^
       twb_lib_loc ^ "/tableau.cma "^
       "pr_o.cmo "^ 
       filename ^ 
       " > "^
       !Options.tmp ^ filename
   in
   ignore(system cmd);
   print_verbose "%s\n" cmd
;; 
 
let rec get_line ch () =
    match Stream.next ch with
    |s when Str.string_match (Str.regexp "^.*.cmo: \\(.*\\)$") s 0 ->
            let l = Str.split (Str.regexp "[ \t]+") (Str.matched_group 1 s) in
            List.map (fun s -> 
                ignore(Str.string_match (Str.regexp "\\(.*\\).cmo") s 0);
                (Str.matched_group 1 s)
            ) l
    |s -> get_line ch ()
;;
 
let rec loop ch l =
    try
        let dl = get_line ch () in
        loop ch (dl@l) 
    with End_of_file |Stream.Failure -> l
;;

let rec deps deplist filename =
    let cmd =
       "ocamldep " ^
       !Options.tmp ^ filename ^
       " > " ^
       !Options.tmp ^ filename ^
       ".deps.txt"
    in
    pp filename;
    ignore(system cmd);
    let fc = open_in (!Options.tmp ^ filename ^ ".deps.txt") in
    let ch = read_lines fc in
    let l = loop ch [] in
    List.append
    deplist
    (List.flatten (List.map (fun f -> deps [f] (f^".ml") ) l))
;;

let compile elem =
    let cmd =
        "ocamlfind ocamlopt -package twb.thelot,twb.cli -c " ^
        "-I " ^ !Options.tmp ^ " "^
        !Options.tmp ^ elem ^ ".ml"
    in
    print_verbose "Compiling: %s\n" cmd;
    ignore(system cmd)
;;

let link l filename =
    let c =
        "ocamlfind ocamlopt -package twb.thelot,twb.cli -linkpkg -o " ^ 
        noext(filename) ^ " "
    in
    let cmd = List.fold_left (fun s f -> s^ !Options.tmp ^ f ^ ".cmx ") c l in
    print_verbose "Linking: %s\n" cmd;
    ignore(system cmd)
;;

let main () =
    let _ =
        try Arg.parse options file usage
        with Arg.Bad s -> failwith s
     in 
    let filename = get(!input_file) in
    (* XXX: the deplist should not have duplicates *)
    let deplist = List.rev (deps [noext(filename)] filename) in
    List.iter compile deplist;
    link deplist filename;
    print_endline "Done.";
;;

let _ = main ()
