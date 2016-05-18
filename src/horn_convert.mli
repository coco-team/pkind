

(** Translate from IL format into sover-specific formulas *)

(** {6 Formulas} *)

val expr_buffer : 
  Types.modetype -> Types.il_expression -> Buffer.t

(** Translate a {!Types.il_formula} into a stringbuffer.  Also perform some bookkeeping for later use. Used for the main program translation. *)
val formula_string_buffer : 
  Types.modetype -> int -> Types.il_formula -> Buffer.t


val simple_formula_buffer : Types.il_formula -> Buffer.t

(** Translate a {!Types.il_formula} into a string.  Do not do any further processing. Used for translation of predetermined formulas (mostly asserts and queries) into solver-specific format.  *)
val simple_command_string : Types.solver_command -> string

(** Returns a string of the program variable definitions.  Also performs some bookkeeping *)
val allVar : unit -> (string * string * string ref * string ref * string * string)

(** Returns a string of the program variable definitions.  Also performs some bookkeeping *)
val allVarRule : unit -> (string * string * string * string * string list * string * string)


(** Returns a string of the formula describing the property predicate P() *)
val property_header : 
  string -> Types.il_expression -> Types.typed_stream -> string

(** Returns a string of the formula describing multiple properties *)
val multi_property_header : 
   string -> Types.il_expression -> Types.typed_stream list -> string

val property_header_new : 
   string -> Types.il_expression -> Types.typed_stream -> string

(** Returns a list of strings of the formula describing the properties *)
val multi_property_header_list : 
   Types.il_expression -> Types.typed_stream list -> string list

(** Returns a string of a formula defining all assumptions (lustre asserts) in the program.  *)
val assumption_string : string -> Types.il_expression -> string

(** Returns a string describing a unique state, based on all variables *)
val state_vars_string : unit -> string 

(** Returns a string describing a unique state based on currently refined variables *)
val state_vars_string_refined : int -> string 

(** Returns the current name of the state_vars definition.  *)
val get_state_vars_r_version : unit -> string

val get_all_def_terms: unit -> Types.il_expression list
