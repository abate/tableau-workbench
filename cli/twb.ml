
open Datatype
open ExtLib
open Loader

module Options =
struct
  let preproc = ref false
  let debug = ref 0
  let noneg = ref false
  let native = ref false

  let timeout = ref 0

  let logic = ref ""
  let libdir = ref "./"

  let outdir = ref "trace"
  let outtype = ref ""

  let native = ref false
end
;;

let usage = "usage: twb [-options] [file]"

let options =
    [
     ("-nopp",  Arg.Clear  Options.preproc,   "disable preproc function");
     ("-noneg", Arg.Set    Options.noneg, "doesn't use the Negation Procedure");

     ("-debug", Arg.Int    (fun l -> Options.debug := l ), "debug level");
     ("-time",  Arg.Int    (fun l -> Options.timeout := l), "set exec timeout");

     ("-logic", Arg.String (fun l -> Options.logic := l),   "set logic");
     ("-dir",   Arg.String (fun l -> Options.libdir := l),   "set library directory");

     ("-outdir",Arg.String (fun l -> Options.outdir := l),  "set output directory");
     ("-out",   Arg.String (fun l -> Options.outtype := l),  "set output type");

     ("-native",Arg.Set Options.native,  "run a prover in native code")
    ]
;;

(** twbpath: location of the twb installation *)
let twbpath =
    try (Sys.getenv "TWBPATH")
    with Not_found -> failwith "Cannot find TWBPATH"
;;

let input_file = ref None;;
let file f =
    try
        match f with
        |s when Str.string_match (Str.regexp "^[\n\t ]*$") s 0 -> ()
        |_ -> input_file := Some(f)
    with _ -> ()
;;

let tree_to_string = function
    Tree.Leaf(n) -> n#to_string
   |_ -> failwith "Something wrong in tree_to_string"
;;

let newnode s =
    let fmap =
        try (new Fmap.map (Option.get (!Logic.__matchpatt)))
        with Option.No_value -> failwith "Rules not specified"
    in
    let hmap =
        try List.fold_left (
                fun m (id,set) -> m#add id set)
            (new Hmap.map) (Option.get (!Logic.__history_list))
        with Option.No_value -> new Hmap.map
    in
    let inputparser =
        try (Option.get (!Logic.__inputparser))
        with Option.No_value -> failwith "Input Parser error"
    in
    let fmap = fmap#addlist (inputparser s) in
    new Node.node (fmap,hmap)
;;

let main () =
    let _ =
        try Arg.parse options file usage
        with Arg.Bad s -> failwith s
    in 
    let _ = 
        if not(!Options.native) then
            Loader.load (twbpath^"/twb/") !Options.libdir !Options.logic
        else print_endline "Native mode"
    in
    let strategy = 
        try (Option.get (!Logic.__strategy))
        with Option.No_value -> failwith "Strategy not specified"
    in
    let file_ch =
        match !input_file with
        |Some(f) -> open_in f
        |None -> stdin
    in
    let read_lines =
        let read_new_line n =
            try Some (input_line file_ch)
            with End_of_file -> None
        in
            Stream.from read_new_line
    in
    let rec get_line () =
        match Stream.next read_lines with
        |s when Str.string_match (Str.regexp "^[\n\t ]+$") s 0 -> get_line ()
        |s -> s
    in
    try
        while true do
            let start = Timer.start_timing () in
            try
                let node = newnode( get_line () ) in
                let _ = Timer.trigger_alarm (!Options.timeout) in
                let proof = Visit.visit strategy strategy#start node in
                let time = Timer.stop_timing start in
                Printf.printf "%s\n%s\n"
                (Timer.to_string time)
                (tree_to_string proof)
            with Timer.Timeout -> Printf.printf "Timeout elapsed\n"
        done
    with
    |End_of_file |Stream.Failure -> exit 0
;;

main ();;
