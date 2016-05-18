open Types
open Exceptions


let gettype (_,ts) = ts

(* typing of nodes is lazy, and currently skips L_UNDET assignments *)
(* returns the type if 2 types are the same *)
let match_types x y =
  let xt = gettype x in
  let yt = gettype y in
  let rec mt2 x1 y1 =
    match x1,y1 with
        L_INT,L_INT -> ()
     |  L_REAL,L_REAL -> ()
     |  L_REAL,L_INT -> ()
     |  L_INT,L_REAL -> ()
     |  L_BOOL,L_BOOL -> ()
     |  L_INT_RANGE(x2,x3),L_INT_RANGE(y2,y3) ->
          if x2!=y2 || x3!=y3 then raise (TypeMismatch("range",xt,yt))
     |  L_REAL_RANGE(x2,x3,x4,x5,x6,x7),L_REAL_RANGE(y2,y3,y4,y5, y6, y7) ->
          if x2!=y2 || x3!=y3 then raise (TypeMismatch("range",xt,yt))
     |  L_TUPLE(x2),L_TUPLE(y2) -> List.iter2 (mt2) x2 y2
     |  L_RECORD(x2),L_RECORD(y2) ->
         begin
         try
           List.iter (fun (fx,tx) ->
             mt2 (List.assoc fx y2) tx
           ) x2
         with Not_found ->
           raise (TypeMismatch("rec",xt,yt))
         end
     |L_INT_RANGE(_), L_INT -> ()
     |L_INT_RANGE(_), L_REAL -> ()
     |L_REAL_RANGE(_), L_REAL -> ()
     |L_REAL_RANGE(_), L_INT -> ()
     | _,_ ->
                 raise (TypeMismatch("match_types mismatch",xt,yt))

  in
  mt2 xt yt;
    if (L_REAL == xt or L_REAL == yt)
    then L_REAL
    else xt

(* checks all types in a list, returns the type list *)
let match_types_list a b =
  try
    List.map2 (match_types) a b
  with TypeMismatch(s,x,y) ->
    Printf.printf "Mismatch in parameter:";
    raise (TypeMismatch("list:"^s,x,y))
  | _ -> failwith "match_types_list"

(* as above for ints only *)
let match_types_int x y =
  let z = match_types x y in
  if z != L_INT then raise (TypeMismatch("int",z,L_INT));
  L_INT

(* as above for bools only *)
let match_types_bool x y =
  let z = match_types x y in
  if z != L_BOOL then raise (TypeMismatch("bool",z,L_BOOL));
  L_BOOL

(* as above, but for numeric relations *)
 let match_types_nrel x y =
  let z = match_types x y in
    match z with
	L_INT -> L_BOOL
      |L_REAL -> L_BOOL
      |L_INT_RANGE(_) -> L_BOOL
      |	_ -> raise (TypeMismatch("nrel",z,L_INT));
  (* if z != L_INT && z != L_REAL  then raise (TypeMismatch("nrel",z,L_INT)); *)
  L_BOOL


(* raises TypeMismatch if is not numeric (real or int) *)
let match_type_is_numeric x =
  let z = gettype x in
  match z with
  | L_INT | L_REAL | L_INT_RANGE _ -> z
  | _ -> raise (TypeMismatch("is_numeric",z,z))

(* returns the type t1 for "ite bool t1 t1" *)
let match_types_ite x y z =
  let xt = gettype x in
  if (xt != L_BOOL) then raise (TypeMismatch("ite",xt,L_BOOL));
  let yt = match_types y z in
  yt


(* raises a TypeMismatch exception if this is not a tuple type *)
(* returns the yth field type *)
let is_tuple_type x y =
  let xt = gettype x in
  match xt with
      L_TUPLE(yt) -> List.nth yt y
    | _ -> raise (TypeMismatch("tup",xt,xt))
