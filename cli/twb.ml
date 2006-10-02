open Datatype
open ExtLib

module Options =
struct
  let nopp = ref false
  let noneg = ref false

  let debug = ref 0
  let trace = ref false
  let timeout = ref 0
  let quite = ref false

  let outdir = ref "trace"
  let outtype = ref ""

  let cache = ref true
end
;;

let usage = "usage: twb [-options] [file]"

let arg_options =
    [
     ("--nopp",  Arg.Set    Options.nopp,  "disable preproc function");
     ("--noneg", Arg.Set    Options.noneg, "disable negation function");

     ("--debug", Arg.Int    (fun l -> Options.debug := l ), "debug level");
     ("--trace", Arg.Set    Options.trace, "print proof trace");
     ("--time",  Arg.Int    (fun l -> Options.timeout := l), "set exec timeout");
     ("--quite", Arg.Set    Options.quite, "print the result only");

     ("--outdir",Arg.String (fun l -> Options.outdir := l),  "set output directory");
     ("--out",   Arg.String (fun l -> Options.outtype := l),  "set output type");

     ("--nocache", Arg.Clear  Options.cache, "disable caching");
    ]
;;

let input_file = ref None;;
let file f =
    try
        match f with
        |s when Str.string_match (Str.regexp "^[\n\t ]*$") s 0 -> ()
        |_ -> input_file := Some(f)
    with _ -> ()
;;

let unbox = function
    Tree.Leaf(n) -> n
    |_ -> failwith "Something wrong in unbox"
;;

let tree_to_string t = (unbox t)#to_string ;;

let newnode s =
    let fmap =
        try (new Fmap.map (Option.get (!Logic.__matchpatt)))
        with Option.No_value -> failwith "Rules not specified"
    in
    let (hmap,vmap) =
        try List.fold_left (
                fun (h,v) ->
                    function
                        |(id,set,History) -> (h#add id set,v)
                        |(id,set,Variable) -> (h,v#add id set)
                    )
            ((new Hmap.map),(new Hmap.map)) (Option.get (!Logic.__history_list))
        with Option.No_value -> (new Hmap.map, new Hmap.map)
    in
    let inputparser =
        try (Option.get (!Logic.__inputparser))
        with Option.No_value -> failwith "Input Parser error"
    in
    let pp = 
        if (!Options.nopp) || Option.is_none (!Logic.__pp)
        then (fun x -> x)
        else (Option.get (!Logic.__pp))
    in 
    let neg = 
        if (!Options.noneg) || Option.is_none (!Logic.__neg)
        then (fun x -> x)
        else (Option.get (!Logic.__neg))
    in 
    let fmap = fmap#addlist (pp ( neg (inputparser s))) in
    new Node.node (fmap,hmap,vmap)
;;

let exit_function t =
    if Option.is_none (!Logic.__exit) then
        let (_,_,v) = (unbox t)#get in
        try
            match v#find "status" with
            `Singleton s -> 
                (match List.hd s#elements with
                |`String s -> s
                |_ -> failwith "exit function not specified and type mismatch")
            |_ -> failwith "exit function not specified"
        with Not_found -> failwith "exit function not specified"
    else
        let (_,_,v) = (unbox t)#get in
        (Option.get (!Logic.__exit)) [v]
;;

let init ?(options=[]) () = 
    let custom_options =
        try (Option.get (!Logic.__options))
        with Option.No_value -> []
    in
    let _ =
        try Arg.parse (options@custom_options) file usage
        with Arg.Bad s -> failwith s
    in 
    let _ = 
        if (Option.is_none !Logic.__printer) then ()
        else Basictype.string_of_formula := (Option.get !Logic.__printer)
    in ()
;;
    
let main () =
    ignore(init ~options:arg_options ());
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
    (* we stop on a new line, we ignore comments *)
    let rec get_line () =
        match Stream.next read_lines with
        |s when Str.string_match (Str.regexp "^[\n\t ]*$") s 0 -> 
                raise End_of_file
        |s when Str.string_match (Str.regexp "^#.*$") s 0 -> get_line ()
        |s -> s
    in
    try
        while true do
            try
                let line = get_line () in
                let _ = 
                    if !Options.quite then ()
                    else Printf.printf "Proving: %s\n" line
                in
                let node = newnode line in
                (* still a bit hackish way of setting user prefs *)
                let _ = UserRule.nodeid := 0 in
                let _ = OutputBroker.trace := !Options.trace in
                let _ = OutputBroker.print node "initial node" 0 in
                let cache = (new Cache.cache !Options.cache) in
            
                let start = Timer.start_timing () in
                let _ = Timer.trigger_alarm (!Options.timeout) in
                let result = Llist.hd (Visit.visit cache strategy node) in
                let time = Timer.stop_timing start in

                Printf.printf "%s\nResult: %s\nTotal Rules applications:%d\n"
                    (Timer.to_string time)
                    (exit_function result)
                    !UserRule.nodeid;

                if !Options.cache then
                    Printf.printf "%s\n\n"
                    cache#stats
                else print_newline ();

                Gc.major ();
                flush_all ()
            with Timer.Timeout -> Printf.printf "Timeout elapsed\n\n"
        done
    with
    |End_of_file |Stream.Failure -> exit 0
;;
