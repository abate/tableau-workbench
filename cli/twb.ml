
exception Timeout
open Unix
open Datatype
open ExtLib

module Logic =
struct
  let strategy : Strategy.state option ref = ref None 
  let matchpatt : (Basictype.mixtype -> string) option ref = ref None
  let inputparser : (string -> Type.bt) option ref = ref None
  let pp : (Type.bt list -> Type.bt list) option ref = ref None
  let neg : (Type.bt list -> Type.bt list) option ref = ref None
  let map : Store.store option ref = ref None
  let hist : History.store option ref = ref None
end

module Options =
struct
  let preproc = ref false
  let debug = ref 0
  let noneg = ref false

  let timeout = ref 0

  let logic = ref ""
  let libdir = ref ""

  let outdir = ref "trace"
  let outtype = ref ""

  let native = ref false
end
;;

let usage = "usage: twb [-options] input-file "

let options =
    [
     ("-nopp",  Arg.Clear  Options.preproc,   "disable preproc function");
     ("-noneg", Arg.Set    Options.noneg, "doesn't use the Negation Procedure");

     ("-debug", Arg.Int    (fun l -> Options.debug := l ), "debug level");
     ("-time",  Arg.Int    (fun l -> Options.timeout := l), "set exec timeout");

     ("-logic", Arg.String (fun l -> Options.logic := l),   "set logic");

     ("-outdir",Arg.String (fun l -> Options.outdir := l),  "set output directory");
     ("-out",   Arg.String (fun l -> Options.outtype := l),  "set output type");

     ("-native",Arg.String (fun l -> Options.outtype := l),  "run a prover in native code")
    ]
;;

(* timeout functions *)
let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout)
let old_behavior = ref (Sys.signal Sys.sigalrm sigalrm_handler)
let update_ob () = old_behavior := Sys.signal Sys.sigalrm sigalrm_handler

let start_timing () =
    let _ = update_ob () in
    let adjust = ref 0.0
    in Unix.times ()
;;

let stop_timing start =
    let stop = Unix.times () in
    ((stop.tms_utime -. start.tms_utime),(stop.tms_stime -. start.tms_stime))
;;

let trigger_alarm () =
    let _ = Unix.alarm !Options.timeout in
    Sys.set_signal Sys.sigalrm !old_behavior
;;

let find_in_path path name =
    let filename = (String.uncapitalize name) ^ ".cmo" in
    if not (Filename.is_implicit filename) then
        if Sys.file_exists filename then filename else raise Not_found
        else
            begin
                let rec try_dir = function
                    | [] -> raise Not_found
                    | dir::rem ->
                            let fullname = Filename.concat dir filename in
                            if Sys.file_exists fullname then fullname
                            else try_dir rem
                in try_dir path
            end


let modules = Hashtbl.create 17;;
let are_loading = Hashtbl.create 17;;
let load_path = [(!Options.libdir)] ;;

let rec load_module modname =
    try
        Hashtbl.find modules modname
    with
        Not_found ->
            try
                Hashtbl.add modules modname ();
                Hashtbl.add are_loading modname ();
                Printf.printf "Loading: %s\n" modname;
                Dynlink.loadfile (modname);
                Hashtbl.remove are_loading modname
            with
            | Dynlink.Error(Dynlink.Unavailable_unit(depend))
            | Dynlink.Error(
                Dynlink.Linking_error(_,Dynlink.Undefined_global(depend))
                ) ->
                    begin
                        try
                            if Hashtbl.mem are_loading depend
                            then failwith ("Crossing with "^depend);
                            load_module (find_in_path load_path depend);
                            Hashtbl.remove modules modname;
                            load_module modname
                        with Not_found ->
                            failwith ("Cannot find "^depend^" in "^
                            (List.fold_left (fun s x -> s^x) " " load_path))
                    end
;;

let init_logic_module () =
        Dynlink.init();
        load_module (find_in_path load_path (!Options.logic))
;;

let tree_to_string = function
    Tree.Leaf(n) -> n#to_string
   |_ -> failwith "Something wrong in tree_to_string"

let main () =
(*    let _ =
        try Arg.parse options file usage
        with Arg.Bad s -> failwith s
    in 
    *)
    let start_state = 
        try (Option.get (!Logic.strategy))
        with Option.No_value -> failwith "Strategy not specified"
    in
    let fmap =
        try (new Fmap.map (Option.get (!Logic.matchpatt)))
        with Option.No_value -> failwith "Rules not specified"
    in
    let hmap = (new Hmap.map) in
    let node = new Node.node (fmap,hmap) in
    try
        while true do
            let start = start_timing () in
            try
                let _ = trigger_alarm () in
                let proof = Visit.visit start_state node in
                let (usertime,systime) = stop_timing start in
                Printf.printf "(user time: %.2f; system time: %.2f)\n%s"
                usertime systime (tree_to_string proof)
            with Timeout -> Printf.printf "Timeout elapsed\n"
        done
    with
    |End_of_file |Stream.Failure -> exit 0
;;

main ();;
