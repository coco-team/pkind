(** A support module for the differet processes *)

(**
@author Temesghen Kahsai

*)


open Flags
open Channels
open Globals
open Types
open ExtList
open ExtString

module type PROC_SUPPORT =
  sig
    val handle_cex: Types.foundvarstable -> int -> unit
    val handle_valid: int -> unit
    val check_valid_input : string -> unit
    val generate_Input_constraint : unit -> unit
  end


module Helper =
struct

  (** Handle counterexamples for BMC process and INDUCT process *)
  let handle_cex foundvars k1 =
    let k_s = string_of_int (k1+1) in
    let _ =  print_to_user_final("\n    MODEL AFTER K ="^k_s^" UNROLLING \n") in
    Kind_support.print_countermodel foundvars 0 k1

 (** Handle valid properties outcome *)
  let handle_valid kappa =
    let k_s = string_of_int kappa in
      if !Flags.xml then (
	print_xml(Kind_support.print_resultProp_xml
		    {result=VALID;
		     foundvars= None;
		     minstep=None;
		     maxstep=None;
		     induct_cex= None;
		     name= "";
		     k=k_s;
		     time=""});
	print_xml ("</Results>");
      ) else (
	print_to_user_final("UNSAT at K ="^k_s^"\n\n")
      )

  let makeDecimal length =
    let k_list = (Array.to_list (Array.init (length) (fun x -> x+1))) in
    let dec = List.fold_right(fun x acc -> "0"^acc) k_list "" in
    "1"^dec

  let createReal x =
    let f,d = String.split x "."  in
    let d_len = String.length d in
    let decimal = makeDecimal d_len in
    "(+ " ^ f ^ " (/ " ^ d ^ " " ^ decimal ^ "))"

  let handleReal i_name val_list k_list =
    let buf = Buffer.create 100 in
    List.iter2 (fun k x ->
		match x with
	  	  " " ->   ()
		| _ ->
		   let i_real = createReal x in
		   Buffer.add_string buf ("(assert  ( = ( " ^ i_name ^ " " ^ string_of_int(k) ^ ")" ^ i_real ^ "))\n"
	       )) (0::k_list) val_list;
    buf

  let handleRest i_name val_list k_list =
    let buf = Buffer.create 100 in
    List.iter2 (fun k x ->
		match x with
	  	  " " ->   ()
		| _ ->    Buffer.add_string buf("(assert  ( = ( " ^ i_name ^ " " ^ string_of_int(k) ^ ")" ^ x ^ "))\n"
	       )) (0::k_list) val_list;
    buf

  (** Generate  input constraint *)
  let generate_Input_Constraint k=
    if not(Sys.file_exists !Flags.sim_filename) then failwith ("Specified file does not exists");
    let input_file = open_in !Flags.sim_filename in
    let all_buf = Buffer.create 100 in
    let k = ref 0 in
    try
      while true do
	let s = input_line input_file in
	let l = Str.split (Str.regexp ",") s in
	let i_name = Tables.original_to_internal (List.hd l) in
	let val_list = List.tl l in
	let k_length = List.length val_list in
        k := k_length;
	let k_list = (Array.to_list (Array.init (k_length-1) (fun x -> x+1))) in
        let buf =
          match Tables.getType i_name with
	    L_REAL ->
            handleReal i_name val_list k_list
	  | _ ->
             handleRest i_name val_list k_list
        in
        Buffer.add_buffer all_buf buf
      done;
      all_buf, !k
    with End_of_file ->
      all_buf, !k
end
