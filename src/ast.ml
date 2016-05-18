open Lsimplify_syntax;;

type sym_table = (string, int) Hashtbl.t
 and id_table  = (int, string) Hashtbl.t;;

(* predefined symbol IDs *)
let undef_sym  = 0;;
let kcomm_main = 1;;
let type_bool  = 2;;
let type_int   = 3;;
let type_real  = 4;;
let val_true   = 5;;
let val_false  = 6;;

(* predefined symbol strings *)
let predef_syms = [
   ("MAIN",  kcomm_main);
   ("bool",  type_bool);
   ("int",   type_int);
   ("real",  type_real);
   ("true",  val_true);
   ("false", val_false);
];;


(* element at key=0 is the global scope.  element at key=1
 * is the local scope *)
let the_sym_tables = (Hashtbl.create 10 :
                      (int, sym_table) Hashtbl.t);;
let the_id_table   = (Hashtbl.create 100 : id_table);;

let create_sym_table () = (Hashtbl.create 100 : sym_table);;

let get_global_sym_table () = Hashtbl.find the_sym_tables 0;;

let get_local_sym_table  () = Hashtbl.find the_sym_tables 1;;

let finish_scope k =
   let local = (get_local_sym_table ()) in
      if k=0 then
         (* TODO - check for redecls here! *)
         let global = (get_global_sym_table ()) in
         Hashtbl.iter (fun k v -> Hashtbl.replace global k v) local
      else (
         try
            let h = Hashtbl.find the_sym_tables k in
            Hashtbl.iter (fun k v ->
               Hashtbl.replace h k v
            ) local
         with Not_found ->
            Hashtbl.add the_sym_tables k (Hashtbl.copy local);
      );
      Hashtbl.clear local
;;

let root_node = ref undef_sym;;
let root_node_flag = ref false;;

Hashtbl.add the_sym_tables 0 (create_sym_table());; (* the global scope key=0 *)
Hashtbl.add the_sym_tables 1 (create_sym_table());; (* the current local scope key=1 *)

(* the total number of symbols we have seen so far (used in
 * assigning IDs to new symbols) *)
let sym_count = ref 0;;

(*let get_sym_name id = let result = Hashtbl.fold (fun k v s ->
   Hashtbl.fold (fun k2 v2 s2 -> if s2<>"" then s2 else 
      (if id=v2 then k2 else "")
) v s) the_sym_tables "" in (if result<>"" then result else ("<"^(string_of_int
id)^">"));;*)

let get_sym_name id =
   try
      ((Hashtbl.find the_id_table id))
   with Not_found ->
      ("<"^(string_of_int id)^">")
;;

let get_next_sym () = (!sym_count + 1);;

let increment_sym_count () = let result = (get_next_sym ()) in
               sym_count := result;
               result;;

type scope = NoScope | GlobalScope | AllScope;;

let add_sym s scp =
   let lt = (get_local_sym_table ()) in
   let gt = (get_global_sym_table ()) in
   let ret = (match scp with
      | NoScope ->
         let inc = increment_sym_count () in
         Hashtbl.add lt s inc;
         Hashtbl.add the_id_table inc s;
         inc
      | GlobalScope ->
         (try
            (* check the global
             * scope *)
            Hashtbl.find gt s
         with Not_found ->
            (* if we can't find the symbol in any scope, add it to the global
             * scope *)
            let inc = increment_sym_count () in
            Hashtbl.add gt s inc;
            Hashtbl.add the_id_table inc s;
            inc)
      | AllScope ->
         try
            (* first look for the symbol in the local scope *)
            Hashtbl.find lt s
         with Not_found ->
            (try
               (* if we don't find the symbol in the local scope, check the global
                * scope *)
               Hashtbl.find gt s
            with Not_found ->
               (* if we can't find the symbol in any scope, add it to the global
                * scope *)
               let inc = increment_sym_count () in
               Hashtbl.add gt s inc;
               Hashtbl.add the_id_table inc s;
               inc)
      ) in ret;;

let create_fresh_sym (id:int) : int =
   let newid = get_next_sym () in
   let newname = (""^(get_sym_name id)^"_"^(string_of_int newid)) in
   add_sym newname NoScope 
;;

let print_sym_table t =
print_string "   [\n";
Hashtbl.iter (fun k v -> 
   print_string "   \"";
   print_string k;
   print_string "\" -> ";
   print_int v;
   print_string "\n"
) t;
print_string "   ]\n";;

let print_symbols () =
   Hashtbl.iter (fun k v ->
   print_string "   Symbols at scope ";
   print_int k;
   print_string "\n";
   print_sym_table v;
) the_sym_tables; print_string "\n";;

(* add the predefined symbals to the global scope *)
let _ = List.iter (fun (s,i) ->
   let _ = add_sym s AllScope in
   ()
) predef_syms in ();;
