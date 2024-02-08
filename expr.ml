(*
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions
 *)

type unop =
  | Negate
;;

type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;

type varid = string ;;

type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;

(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;

(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let rec free_vars (exp : expr) : varidset =
  let set = SS.empty in
  match exp with
  | Var (id) -> SS.add id set
  | Num (_) -> set
  | Bool (_) -> set
  | Unop (_, ex) -> (free_vars ex)
  | Binop (_, ex1, ex2) -> SS.union (free_vars ex1) (free_vars ex2)
  | Conditional (ex1, ex2, ex3) -> SS.union (SS.union (free_vars ex2) (free_vars ex3)) (free_vars ex1)
  | Fun (id, ex) -> SS.remove id (free_vars ex)
  | Let (id, ex1, ex2) -> SS.union (free_vars ex1)
                            (SS.remove id (free_vars ex2))
  | Letrec (id, ex1, ex2) -> SS.union (SS.remove id (free_vars ex1))
                            (SS.remove id (free_vars ex2))
  | Raise -> set
  | Unassigned -> set
  | App (ex1, ex2) -> SS.union (free_vars ex1) (free_vars ex2)

(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)
let new_varname () : varid =
  let suffix = ref 0 in
  let new_var = "var" ^ string_of_int !suffix in
                suffix := !suffix + 1;
                new_var ;;

(*......................................................................
  Substitution

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
let subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  (* create set of free variables and check var_name found within *)
  let frees = free_vars exp in
  if not(SS.mem var_name frees) then exp
  else
    (* iterate through expression substituting in repl if we find an free
       variable which is named var_name *)
    let rec inner_subst ?(var_name : varid = var_name) ?(repl : expr = repl)
        (exp : expr) : expr =
      match exp with
      | Var (st) -> if st = var_name then repl
        else Var(st)
      | Num (x) -> Num (x)
      | Bool (tf) -> Bool (tf)
      | Unop (un, ex) -> Unop (un, inner_subst ex)
      | Binop (bi, ex1, ex2) -> Binop (bi, inner_subst ex1, inner_subst ex2)
      | Conditional (ex1, ex2, ex3) -> Conditional
          (inner_subst ex1, inner_subst ex2, inner_subst ex3)
      | Fun (st, ex1) ->
        if st = var_name then Fun(st, ex1)
        else if SS.mem st (free_vars repl) then
          let new_var = new_varname () in
          inner_subst (Fun
                (new_var, inner_subst ~var_name:st ~repl:(Var(new_var)) ex1))
        else
          Fun (st, inner_subst ex1)
      | Let (st, ex1, ex2) ->
        if st = var_name then Let(st, inner_subst ex1, ex2)
        (* if st is contained within repl as a free variable we must rename *)
        else if SS.mem st (free_vars repl) then
          let new_var = new_varname () in
          inner_subst (Let
          (new_var, ex1, inner_subst ~var_name:st ~repl:(Var(new_var)) ex2))
        (* if all involved variables are distinct i.e. no worrying obstacles *)
        else
          Let(st, inner_subst ex1, inner_subst ex2)
      | Letrec (st, ex1, ex2) ->
        if st = var_name then Letrec(st, ex1, ex2)
        else if SS.mem st (free_vars repl) then
          let new_var = new_varname () in
          inner_subst (Letrec
            (new_var, ex1, inner_subst ~var_name:st ~repl:(Var(new_var)) ex2))
        else
          Letrec(st, inner_subst ex1, inner_subst ex2)
      | Raise -> Raise
      | Unassigned -> Unassigned
      | App (ex1, ex2) -> App(inner_subst ex1, inner_subst ex2) in
    inner_subst exp ;;

(*......................................................................
  String representations of expressions
 *)


(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var (st) -> Printf.sprintf "%s" st
  | Num (x) -> Printf.sprintf "%i" x
  | Bool (tf) -> Printf.sprintf "%B" tf
  | Unop (un, ex) ->
    (match un with
     | Negate -> "(-" ^ (exp_to_concrete_string ex)) ^ ")"
  | Binop (bi, ex1, ex2) ->
    (match bi with
     | Plus -> "(" ^ (exp_to_concrete_string ex1) ^ " + "
               ^ (exp_to_concrete_string ex2) ^ ")"
     | Minus -> "(" ^ (exp_to_concrete_string ex1) ^ " - "
                ^ (exp_to_concrete_string ex2) ^ ")"
     | Times -> "(" ^ (exp_to_concrete_string ex1) ^ " * "
                ^ (exp_to_concrete_string ex2) ^ ")"
     | Equals -> "(" ^ (exp_to_concrete_string ex1) ^ " = "
                 ^ (exp_to_concrete_string ex2) ^ ")"
     | LessThan -> "(" ^ (exp_to_concrete_string ex1) ^ " < "
                   ^ (exp_to_concrete_string ex2) ^ ")")
  | Conditional (ex1, ex2, ex3) -> "if " ^ (exp_to_concrete_string ex1) ^ " then "
                                   ^ (exp_to_concrete_string ex2)
                                   ^ " else " ^ (exp_to_concrete_string ex3)
  | Fun (st, ex) -> "fun " ^ (Printf.sprintf "%s" st) ^ " -> "
                    ^ (exp_to_concrete_string ex)
  | Let (st, ex1, ex2) -> "let " ^ (Printf.sprintf "%s" st) ^ " = "
                          ^ (exp_to_concrete_string ex1) ^ " in "
                          ^ (exp_to_concrete_string ex2)
  | Letrec (st, ex1, ex2) -> "let rec " ^ (Printf.sprintf "%s" st) ^ " = "
                             ^ (exp_to_concrete_string ex1) ^ " in "
                             ^ (exp_to_concrete_string ex2)
  | Raise -> "EXCEPTION"
  | Unassigned -> "UNASSIGNED"
  | App (ex1, ex2) -> (exp_to_concrete_string ex1) ^ " "
                      ^ (exp_to_concrete_string ex2) ;;


(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let exp_to_abstract_string (exp : expr) : string =
  let rec convert (exp : expr) : string =
    match exp with
    | Var (st) -> Printf.sprintf "Var(%s)" st
    | Num (x) -> Printf.sprintf "Num(%i)" x
    | Bool (tf) -> Printf.sprintf "Bool(%B)" tf
    | Unop (un, ex) ->
      (match un with
       | Negate -> Printf.sprintf "Unop(Negate, %s)" (convert ex))
    | Binop (bi, ex1, ex2) ->
      (match bi with
       | Plus ->
         Printf.sprintf "Binop(Plus, %s, %s)" (convert ex1) (convert ex2)
       | Minus ->
         Printf.sprintf "Binop(Minus, %s, %s)" (convert ex1) (convert ex2)
       | Times ->
         Printf.sprintf "Binop(Times, %s, %s)" (convert ex1) (convert ex2)
       | Equals ->
         Printf.sprintf "Binop(Equals, %s, %s)" (convert ex1) (convert ex2)
       | LessThan ->
         Printf.sprintf "Binop(LessThan, %s, %s)" (convert ex1) (convert ex2))
    | Conditional (ex1, ex2, ex3) -> Printf.sprintf "Conditional(%s, %s, %s)"
                                      (convert ex1) (convert ex2) (convert ex3)
    | Fun (st, ex) -> Printf.sprintf "Fun(%s, %s)" st (convert ex)
    | Let (st, ex1, ex2) -> Printf.sprintf "Let(%s, %s, %s)"
                              st (convert ex1) (convert ex2)
    | Letrec (st, ex1, ex2) -> Printf.sprintf "Letrec(%s, %s, %s)"
                                 st (convert ex1) (convert ex2)
    | Raise -> "EXCEPTION"
    | Unassigned -> "UNASSIGNED"
    | App (ex1, ex2) -> Printf.sprintf "App(%s, %s)"
                          (convert ex1) (convert ex2) in
  convert exp;;
