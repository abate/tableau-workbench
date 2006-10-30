
open Unix
open Str
open Findlib


module Options = struct
    let verbose = ref false
    let compileonly = ref false
    let output = ref ""
    let bytecode = ref false
    let custom = ref ""
    
    let clean = ref false
    
    let tmp = ref ""
end
;;

(* Findlib.init () ;; *)

let options = [
    ("-v",  Arg.Set Options.verbose, "verbose");
    ("-c",  Arg.Set Options.compileonly, "compile only (do not link)");
    ("-b",  Arg.Set Options.bytecode, "bytecode");
    ("-o",  Arg.Set_string Options.output,  "<file> Set output file name to <file>");
    ("--custom", Arg.Set_string Options.custom, "<obj> custom init");
    
    ("-t",  Arg.Set_string Options.tmp,  "temporary directory");
    
    ("--clean", Arg.Set Options.clean, "clean the temporary directory")
]
;;

let usage = "usage: compile [-options] <files>" ;;

let input_filelist = ref [];;
let file f =
    try
        match f with
        |s when Str.string_match (Str.regexp "^[\n\t ]*$") s 0 -> ()
        |s ->
                let l = Str.split (Str.regexp "[ \t]+") s in
                input_filelist := !input_filelist @ l
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

let tmp_dir =
    match !Options.tmp with
    |"" ->
            let str = "/tmp/twb" ^ Unix.getlogin () in
            let _ = 
                try ignore(Unix.stat str) with
                |Unix.Unix_error(_) -> ignore(Unix.mkdir str 0o755)
            in str ^ "/"
    |s -> s ^ "/"
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
       twb_lib_loc ^ "/pa_tableau.cma "^
       "pr_o.cmo "^ 
       filename ^ 
       " > "^
       tmp_dir ^ filename
   in
   ignore(system cmd);
   print_verbose "%s\n" cmd
;; 
 
let rec get_line ch () =
    let aux s =
        let ms = Str.replace_first (Str.regexp "\\") "" (Str.matched_group 1 s) in
        let l = Str.split (Str.regexp "[ \t]+") ms in
        List.map (fun s -> 
            ignore(Str.string_match (Str.regexp "\\(.*\\).cmo") s 0);
            (Str.matched_group 1 s)
        ) l
    in
    match Stream.next ch with
    |s when Str.string_match (Str.regexp "^.*.cmo: \\(.*\\)$") s 0 ->
            aux s
    |s when Str.string_match (Str.regexp "^\\(.*.cmo[^:].*\\)$") s 0 ->
            aux s
    |s -> get_line ch ()
;;
 
let rec loop ch l =
    try
        let dl = get_line ch () in
        loop ch (dl@l) 
    with End_of_file |Stream.Failure -> l
;;

let rec uniq = function
    |[] -> []
    |h::t -> h:: uniq (List.filter (fun x -> not(x = h)) t)
;;

let rec deps deplist filename =
    let cmd =
       "ocamldep " ^
       tmp_dir ^ filename ^
       " > " ^
       tmp_dir ^ filename ^
       ".deps.txt"
    in
    pp filename;
    ignore(system cmd);
    let fc = open_in (tmp_dir ^ filename ^ ".deps.txt") in
    let ch = read_lines fc in
    let l = loop ch [] in
    List.append
    deplist
    (List.flatten (List.map (fun f -> deps [f] (f^".ml") ) l))
;;

let compile elem =
    let ocaml = if !Options.bytecode then "ocamlc" else "ocamlopt" in
    let cmd =
        "ocamlfind "^ ocaml ^" -package twb.thelot,twb.cli -c -unsafe -noassert " ^
        "-I " ^ tmp_dir ^ " "^
        tmp_dir ^ elem ^ ".ml"
    in
    print_verbose "Compiling: %s\n" cmd;
    ignore(system cmd)
;;

let link l filename =
    let ocaml = if !Options.bytecode then "ocamlc" else "ocamlopt" in
    let ext = if !Options.bytecode then ".cmo " else ".cmx " in
    let c =
        "ocamlfind "^
        ocaml ^
        " -package twb.thelot,twb.cli -unsafe -noassert -linkpkg -o "^ 
        filename ^" "
    in
    let cmd = List.fold_left (fun s f -> s^ tmp_dir ^ f ^ ext) c l in
    if !Options.custom = "" then begin
        print_verbose "Linking: %s\n" (cmd ^ " twb.cmx");
        ignore(system (cmd ^ " twb.cmx"))
        end
    else
        begin
            print_verbose "Linking: %s\n" (cmd ^ !Options.custom);
            ignore(system (cmd ^ " " ^ !Options.custom))
        end
;;

let remove_files () =
    let cmd = "rm -f "^tmp_dir^"*.cm*" in
    ignore(system cmd);
    print_verbose "Cleaning: %s\n" cmd
;;

let main () =
    let _ =
        try Arg.parse options file usage
        with Arg.Bad s -> failwith s
    in
    if !Options.clean then ( remove_files (); exit(1) )
    else
        List.iter( fun filename ->
            (* XXX: the deplist should not have duplicates *)
            let deplist = uniq(List.rev (deps [noext(filename)] filename)) in
            List.iter compile deplist;
            if not(!Options.compileonly) then begin
                let output =
                    if !Options.output = "" then (noext(filename)^".twb")
                    else !Options.output
                in link deplist output;
            end;
        ) !input_filelist ;
        print_endline "Done."
;;

let _ = main ()
