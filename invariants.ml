open Printf

(* Définitions de terme, test et programme *)

type term =
 | Const of int
 | Var of int
 | Add of term * term
 | Mult of term * term

type test =
 | Equals of term * term
 | GreaterThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = GreaterThan (Const 0, Const 0)

type program = {nvars : int;
                inits : int list;
                mods : term list;
                loopcond : test;
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term : term -> string`
   et `str_of_test : test -> string` qui convertissent des termes
   et des tests en chaînes de caractères du format SMT-LIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)". *)

let rec str_of_term t = 
  match t with
  |Var v -> "x" ^ string_of_int v
  |Const c -> string_of_int c
  |Add (x, y) -> "(+ " ^ (str_of_term x) ^ " " ^ (str_of_term y) ^ ")" 
  |Mult (x, y) -> "(* " ^ (str_of_term x) ^ " " ^ (str_of_term y) ^ ")"  

let str_of_test t = 
  match t with
  |Equals (x, y) -> "(= " ^ (str_of_term x) ^ " " ^ (str_of_term y) ^ ")" 
  |GreaterThan (x, y) -> "(> " ^ (str_of_term x) ^ " " ^ (str_of_term y) ^ ")" 

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction `str_condition : term list -> string`
   qui prend une liste de termes t1, ..., tk et retourne une chaîne
   de caractères qui exprime que le tuple (t1, ..., tk) est dans
   l'invariant.  Par exemple, str_condition [Var 1; Const 10] retourne
   "(Invar x1 10)". *)

let str_condition l = 
  let rec aux l =
    match l with
    |[] -> ")"
    |h::q -> str_of_term h ^ " " ^ aux q
  in "(Invar " ^ aux l

(* Question 3. Écrire une fonction
   `str_assert_for_all : int -> string -> string` qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMT-LIB qui correspond à la formule "forall x1 ... xk
   (s)".

  Par exemple, str_assert_forall 2 "> x1 x2" retourne : "(assert
   (forall ((x1 Int) (x2 Int)) (> x1 x2)))".  *)

let str_assert s = "(assert " ^ s ^ ")"

let str_assert_forall n s =
  let variables = List.init n (fun i -> "( x" ^ string_of_int (i+1) ^ " Int )") in
  str_assert ("(forall (" ^ String.concat " " variables ^ ") " ^ s ^ ")")

let list_of_var nb = List.init nb (fun i -> Var (i+1))

(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)
let str_of_test_negation t = 
  match t with
  |Equals (x, y) -> "(!= " ^ (str_of_term x) ^ " " ^ (str_of_term y) ^ ")" 
  |GreaterThan (x, y) -> "(<= " ^ (str_of_term x) ^ " " ^ (str_of_term y) ^ ")" 

let str_implication p = "(=> (and " ^ (str_condition (list_of_var p.nvars)) ^ " " ^ (str_of_test p.loopcond) ^ ") " ^ str_condition p.mods ^ ")"

let str_assertation p = 
  match p.loopcond with
  |GreaterThan _ ->
    "(=> (and " ^ (str_condition (list_of_var p.nvars)) ^ " " ^ (str_of_test_negation p.loopcond) ^ ") " ^ str_of_test p.assertion ^ ")"
  |Equals _ ->
    "(=> (and " ^ (str_condition (list_of_var p.nvars)) ^ " " ^ (str_of_test_negation p.loopcond) ^ ") " ^ str_of_test p.assertion ^ ")"

let smtlib_of_wa p =
  let declare_invariant =
    "; synthèse d'invariant de programme\n"
    ^ "; on déclare le symbole non interprété de relation Invar\n"
    ^ "(declare-fun Invar (" ^ string_repeat "Int " p.nvars ^  ") Bool)" in
  let loop_condition =
    "; la relation Invar est un invariant de boucle\n"
    ^ str_assert_forall p.nvars (str_implication p) in
  let initial_condition =
    "; la relation Invar est vraie initialement\n"
    ^ str_assert (str_condition (List.map (function i -> Const i) p.inits)) in
  let assertion_condition =
    "; l'assertion finale est vérifiée\n"
    ^ str_assert_forall p.nvars (str_assertation p) in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant;
                      loop_condition;
                      initial_condition;
                      assertion_condition;
                      call_solver]

let p1 = {nvars = 2;
          inits = [4 ; 0];
          mods = [Add ((Var 1), (Const (-1))); Add ((Var 2), (Var 1))];
          loopcond = GreaterThan ((Var 1), (Const 0));
          assertion = Equals ((Var 2),(Const 10))}

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMT-LIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. *)

let () = Printf.printf "%s" (smtlib_of_wa p1)

(* Ajoutez dans la variable p2 ci-dessous au moins un autre programme
   test avec **trois** variables et vérifiez qu'il donne un fichier
   SMT-LIB la forme attendue. *)

let p2 = {nvars = 3;
          inits = [4 ; 42; 55];
          mods = [Add ((Var 1), (Const (-8))); 
          Mult ((Var 2), (Const 10));
          Add ((Var 3), (Const 14))];
          loopcond = GreaterThan ((Var 1), (Const (-50)));
          assertion = GreaterThan ((Var 3),(Const 150))}

let () = Printf.printf "%s" (smtlib_of_wa p2)
