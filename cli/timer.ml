
exception Timeout
open Unix

(* timeout functions *)
let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout)
let old_behavior = ref (Sys.signal Sys.sigalrm sigalrm_handler)
let update_ob () = old_behavior := Sys.signal Sys.sigalrm sigalrm_handler

let start_timing () =
    let _ = update_ob () in
    (* let adjust = ref 0.0 in *)
    Unix.times ()
;;

let stop_timing start =
    let stop = Unix.times () in
    ((stop.tms_utime -. start.tms_utime),(stop.tms_stime -. start.tms_stime))
;;

let trigger_alarm timeout =
    let _ = Unix.alarm timeout in
    Sys.set_signal Sys.sigalrm !old_behavior
;;

let to_string (usertime,systime) =
    Printf.sprintf "(user time: %.2f; system time: %.2f)"
    usertime systime
;;
