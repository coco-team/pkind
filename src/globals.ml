(** Global variables & functions *)

(**
@author Temesghen Kahsai

*)

open Types
open Exceptions
open Mpi

let version = "1.8.7"
let build = "2013/04/04"

class current_solver =
object
  val mutable s = new Solver_base.solver_base
  method set s1 = s <- s1
  method get = (s :> Solver_base.solver_base)
end

let my_solver = new current_solver

let firsttime = ref true (* true if fist time through main loop *)
let stop = ref false  (* set to true if main loop is done *)
let error = ref false (* set to true if error encountered in solver *)
(*let counter_stop = ref false   set to true when in parallel you find a counterexample*)

let base_abstr = 0
let step_abstr = 1

let max_num_digits = 9


(** For generation of invariants of type intervals*)
let is_inter = ref false

(** Parallel processes *)
let proc_size = comm_size comm_world  (* comm_size, comm_rank *)
let proc_rank = comm_rank comm_world
let base_proc = 0
let step_proc = 1
let inv_gen_proc = ref 2
let kind_ai_proc = ref 3
let base_stop = ref false
let stop_inv_gen = ref false

(** Wall time *)
let master_time_start  =  ref 0.0
let master_time_stop  =  ref 0.0
let base_time_start  = ref 0.0
let base_time_stop  = ref 0.0
let step_time_start  = ref 0.0
let step_time_stop  = ref 0.0
let inv_gen_time_start  = ref 0.0
let inv_gen_time_stop  = ref 0.0
let bool_inv_gen_time_start  = ref 0.0
let bool_inv_gen_time_stop  = ref 0.0
let int_inv_gen_time_start  = ref 0.0
let int_inv_gen_time_stop  = ref 0.0
let kind_ai_time_start = ref 0.0
let kind_ai_time_stop  = ref 0.0

(** Generation of xml document *)
let xml = ref false

(** Storing the specified property. This is needed for single property verification.*)
let prop_specified = ref ""

let prop_typed_stream = ref (S_TRUE,L_BOOL)


(** Get the initial state or transition relation *)
let whichState = ref false
