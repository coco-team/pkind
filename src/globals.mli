(** Global variables & functions *)

(**
@author Temesghen Kahsai
*)




(** Strings denoting version information *)
val version : string
val build : string

(** The [current_solver] class is used to store the actual solver interface.*)
class current_solver :
object
  val mutable s : Solver_base.solver_base
  method set : Solver_base.solver_base -> unit (** Store a solver interface *)
  method get : Solver_base.solver_base (** The currently stored solver interface *)
end

val my_solver : current_solver


val firsttime : bool ref (** True if first time through main loop *)
val stop : bool ref  (** Set to true if main loop is done *)
val error : bool ref (** Set to true if error encountered in main loop *)

val base_abstr : int (** The index for the base abstraction *)
val step_abstr : int (** The index for the step abstraction *)

val max_num_digits: int (** The max number of digits allowed **)


(** For generation of invariants of type intervals*)
val is_inter : bool ref

(** Parallel processes *)
val proc_size : int
val proc_rank : int
val base_proc : int
val step_proc : int
val inv_gen_proc : int ref
val kind_ai_proc: int ref
val base_stop : bool ref
val stop_inv_gen : bool ref

(** Wall time *)
val base_time_start : float ref
val base_time_stop : float ref
val step_time_start : float ref
val step_time_stop : float ref
val inv_gen_time_start : float ref
val inv_gen_time_stop : float ref
val bool_inv_gen_time_start  : float ref
val bool_inv_gen_time_stop  : float ref
val int_inv_gen_time_start  : float ref
val int_inv_gen_time_stop  : float ref
val kind_ai_time_start  : float ref
val kind_ai_time_stop  : float ref


(** Generation of xml document *)
val xml : bool ref

(** Storing the specified property. This is needed for single property verification.*)
val prop_specified : string ref


val prop_typed_stream : Types.typed_stream ref


(** Get the initial state or transition relation *)
val whichState : bool ref
