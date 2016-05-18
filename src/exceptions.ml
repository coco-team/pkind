(* all exceptions *)

open Types

(* lus_convert.ml *)
exception ConversionError of string
exception IdNotFound of string
exception Def_Not_Found of int
exception SimplifyPositionException
exception COIException
exception TypeMismatch of string * lustre_type * lustre_type
exception IncorrectTypedConversion of string
exception NotSupportedType
exception TooManyOutputs
exception NoStatefulVars
exception AllStatefulVarsRefined
exception Reachable_space_explored


(* kind_support.ml *)
exception Error_found of string
exception Timeout
exception Incomplete_code of string
exception RefineAbstraction of check_type
exception No_next_refinement_step
exception Reachable_space_explored
exception SolverError of string
exception UNSAT_FOUND


(* coi.ml *)
exception Incorrect_formula
exception Expr_not_supported
exception Redefinition
exception EmptyLHS


(* defgen.ml *)
exception Lus_convert_error
exception Unguarded_PRE

(* inlining.ml, structural.ml  *)
exception Not_supported of string


(* Invariant generation *)

exception EQUIV_CLS_STABLE
exception SOLVER_ERROR

(* parallel kind *)
exception Wrong_number_of_proc of int * int
