(* ############################################### *)
(* # AUTHOR : Nicolas Stadler                    # *)
(* # EMAIL : nicolas.stadler@etu.umontpellier.fr # *)
(* ############################################### *)


(*############################################################# DATA TYPES #############################################################*)

(* Literal (variable or constant) *)
type literal =
  | Variable of string                 (* x *)
  | Function of string * literal list  (* f(x, y) *)

(* Expression (made up of other expressions) *)
type expression = 
    Atom of string * literal list          (* P(x) *)
  | Not of expression                      (* ¬A *)
  | Or of expression * expression          (* A ∨ B *)
  | And of expression * expression         (* A ∧ B *)
  | Implies of expression * expression     (* A => B *)
  | Equivalent of expression * expression  (* A <=> B *)
  | Forall of literal * expression         (* ∀x.P(x) *) 
  | Exists of literal * expression         (* ∃x.P(x) *)

(* Simple type for atoms or negated atoms, to be used only after the formula is in CNF *)
type atom = 
    PosAtom of string * literal list  (* P(x) *)
  | NegAtom of string * literal list  (* ~P(x) *)
  | False

(* constants type that acts as a global index to keep generating new constant names during skolemisation *)
type constants = { index : int ref };;
let cons = { index = ref (-1) };;

(*############################################################# STRING FUNCTIONS #############################################################*)

(* Returns a string from a literal, as x if x is a variable or "x" if x is a constant *)
let rec string_of_literal literal =
  match literal with
  | Variable x -> x 
  | Function (x, []) -> String.concat "" ("'" :: x :: "'" :: [])
  | Function (x, y) -> String.concat "" (x :: "(" :: (string_of_literals y) :: ")" :: [])

(* Returns a string from a list of literals, as x, y, z *)
and string_of_literals literals =
  String.concat ", " (List.map (string_of_literal) literals)

(* Returns a string from an expression, as ¬(P(a) => ¬(Q(b) ∧ P(c))) *)
and string_of_expression expr = 
  match expr with
    Atom (x,y) -> String.concat "" (x :: "(" :: (string_of_literals y) :: ")" :: [])                                        (* "P(x)" *)
  | Not x -> String.concat "" ("~" :: string_of_expression x :: [])                                                         (* "~P(x)" *)
  | Or (x,y) -> String.concat "" ("(" :: string_of_expression x :: " | " :: string_of_expression y :: ")" :: [])            (* "(P(x) | Q(x))" *)
  | And (x,y) -> String.concat "" ("(" :: string_of_expression x :: " & " :: string_of_expression y :: ")" :: [])           (* "(P(x) & Q(x))" *)
  | Implies (x,y) -> String.concat "" ("(" :: string_of_expression x :: " => " :: string_of_expression y :: ")" :: [])      (* "(P(x) => Q(x))" *)
  | Equivalent (x,y) -> String.concat "" ("(" :: string_of_expression x :: " <=> " :: string_of_expression y :: ")" :: [])  (* "(P(x) <=> Q(x))" *)
  | Forall (x,y) -> String.concat "" ("(V" :: string_of_literal x :: "." :: string_of_expression y :: ")" :: [])            (* "(Vx.A)" *)
  | Exists (x,y) -> String.concat "" ("(E" :: string_of_literal x :: "." :: string_of_expression y :: ")" :: []);;          (* "(Ex.A)" *)

(* Returns a string from an atom, as p(x,y,z) or ~p(x,y,z) *)
let string_of_atom atom = 
  match atom with 
    NegAtom (x,y) -> String.concat "" ("~" :: x :: "(" :: (string_of_literals y) :: ")" :: [])
  | PosAtom (x,y) -> String.concat "" (x :: "(" :: (string_of_literals y) :: ")" :: [])
  | False -> "x";;

(* Returns a string from a clause (list of atoms), as [p1, p2, ...] *)
let string_of_clause atoms = 
  String.concat "" ("[" :: String.concat ", " (List.map (string_of_atom) atoms) ::"]" :: []);;

(* Returns a string from a cnf (list of clauses), as [c1] ; [c2] ; ... *)
let string_of_cnf clauses =
  String.concat " ; " (List.map (string_of_clause) clauses);;

(*############################################################# SIMPLIFICATION #############################################################*)

(* Takes the list of an atoms literals and transforms the one equal to var into a function of unbound variables *)
let rec assign_atom arguments var unbound =
  match arguments with 
    [] -> []
  | h::t -> if h = var then 
      (match unbound with 
         [] ->                                                                       (* if there is no unbound variable, assign a constant instead *)
         let label = String.concat "" ("c" :: string_of_int !(cons.index) :: []) in
         [Function(label, [])]
       | _ -> let label = String.concat "" ("f" :: string_of_int !(cons.index) :: []) in
         Function(label, unbound)::(assign_atom t var unbound))
    else h::(assign_atom t var unbound);;                                            (* for each argument equal to var, replace it with a function of all unbound variables *)

(* Returns a list of all unbound variables in an atom *)
let rec unbound_variables_in_atom arguments bound =
  match arguments with 
    [] -> []
  | h::t -> if List.mem h bound then unbound_variables_in_atom t bound else  (* for each argument, if it is bound by a quantifier, remove it from the list *)
      (match h with
         Function (x, []) -> unbound_variables_in_atom t bound                   (* also make sure the argument isn't a constant *)
       | _ -> h::(unbound_variables_in_atom t bound));;

(* Removes duplicate elements from the list *)
let rec cleanup_duplicates list = 
  match list with
    [] -> []
  | h::t -> if List.mem h t then cleanup_duplicates t else h::(cleanup_duplicates t);;

(* Returns the list of unbound variables in expr *)
let rec unbound_variables ?(bound=[]) expr =
  match expr with 
    Forall (x,y) | Exists (x,y) -> unbound_variables ~bound:(x::bound) y
  | Not x -> unbound_variables ~bound x                                       
  | And (x,y) | Or (x,y) | Implies (x,y) | Equivalent (x,y) -> 
    List.rev_append (unbound_variables ~bound x) (unbound_variables ~bound y)
  | Atom (x,y) -> unbound_variables_in_atom y bound;;

(* Returns expr[f(x1, ... , xn)/var] where x1, ... , xn are the unbound variables of expr and var is the quantified variable  *)
let rec assign ?(i=0) expr ?(unbound = (unbound_variables expr)) var =
  print_endline (String.concat "" ("Assigning:     " :: String.make i ' ' :: (string_of_expression expr) :: " with unbound variables: " :: string_of_literals unbound :: []));
  match expr with 
    Forall (x,y) | Exists (x,y) -> assign ~i:(i + 1) y ~unbound var                                           (* ∀x.Φ or ∃x.Φ ---> Add x to bound variables *)
  | Not x -> assign x ~unbound var                                                                            (* Φ ---> Do nothing, simply make a recursive call *)
  | And (x,y) -> And( (assign ~i:(i + 1) x ~unbound var), (assign ~i:(i + 1) y ~unbound var) )
  | Or (x,y) -> Or( (assign ~i:(i + 1) x ~unbound var), (assign ~i:(i + 1) y ~unbound var) )
  | Implies (x,y) -> Implies( (assign ~i:(i + 1) x ~unbound var), (assign ~i:(i + 1) y ~unbound var) )
  | Equivalent (x,y) -> Equivalent( (assign ~i:(i + 1) x ~unbound var), (assign ~i:(i + 1) y ~unbound var) )
  | Atom (x,y) -> Atom(x , assign_atom y var (cleanup_duplicates unbound));;                                  (* s(∀x.∃y.∀z.P(x, y, z)) ---> P(x, f(x), z) *)

(* Returns the Skolem form corresponding to expr *)
let rec skolem ?(i=0) expr =
  print_endline (String.concat "" ("Skolemizing:   " :: String.make i ' ' :: (string_of_expression expr) :: []));
  match expr with
    Or (x,y) -> Or( (skolem ~i:(i + 1) x), (skolem ~i:(i + 1) y) )              (* s(Φ ∨ Φ') ---> s(Φ) ∨ s(Φ') *)
  | And (x,y) -> And( (skolem ~i:(i + 1) x), (skolem ~i:(i + 1) y) )            (* s(Φ ∧ Φ') ---> s(Φ) ∧ s(Φ') *)
  | Not x -> Not(herbrand ~i:(i + 1) x)                                         (* s(¬Φ) ---> ¬h(Φ) *)
  | Implies (x,y) -> Implies( (herbrand ~i:(i + 1) x), (skolem ~i:(i + 1) y) )  (* s(Φ => Φ') ---> h(Φ) => s(Φ') *)
  | Forall (x,y) -> skolem ~i:(i + 1) y                                         (* s(∀x.Φ) ---> s(Φ) *)
  | Exists (x,y) -> 
    cons.index := !(cons.index) + 1;
    skolem ~i:(i + 1) (assign ~i expr x)                                        (* s(∃x.Φ) ---> s(Φ)[f (x1, ... , xn)/x] *)
  | _ -> expr                                                                   (* s(Φ) ---> Φ *)

(* Returns the Herbrand form corresponding to expr *)
and herbrand ?(i=0) expr =
  print_endline (String.concat "" ("Herbrandizing: " :: String.make i ' ' :: (string_of_expression expr) :: []));
  match expr with
    Or (x,y) -> Or( (herbrand ~i:(i + 1) x), (herbrand ~i:(i + 1) y) )          (* h(Φ ∨ Φ') ---> h(Φ) ∨ h(Φ') *)
  | And (x,y) -> And( (herbrand ~i:(i + 1) x), (herbrand ~i:(i + 1) y) )        (* h(Φ ∧ Φ') ---> h(Φ) ∧ h(Φ') *)
  | Not x -> Not(skolem ~i:(i + 1) x)                                           (* h(¬Φ) ---> ¬s(Φ) *)
  | Implies (x,y) -> Implies( (skolem ~i:(i + 1) x), (herbrand ~i:(i + 1) y) )  (* h(Φ => Φ') ---> s(Φ) => h(Φ') *)
  | Forall (x,y) -> 
    cons.index := !(cons.index) + 1;
    herbrand ~i:(i + 1) (assign ~i expr x)                                      (* h(∀x.Φ) ---> h(Φ)[f (x1, ... , xn)/x] *)
  | Exists (x,y) -> herbrand ~i:(i + 1) y                                       (* h(∃x.Φ) ---> h(Φ) *)
  | _ -> expr;;                                                                 (* h(Φ) ---> Φ *)

(* Returns the expression in its recursive CNF *)
let rec simplify ?(i=0) expr = 
  print_endline (String.concat "" ("Simplifying:   " :: String.make i ' ' :: string_of_expression expr :: []));
  let result = 
    match expr with 
      Atom (x,y) -> Atom(x,y)                                               (* P(x) ---> P(x) *)
    | Not x -> 
      (match x with
         Not a -> x                                                         (* ¬¬A ---> A *)
       | And (a,b) -> Or( Not(a), Not(b) )                                  (* ¬(A ∨ B) ---> ¬A ∧ ¬B *)
       | Or (a,b) -> And( Not(a), Not(b) )                                  (* ¬(A ∧ B) ---> ¬A) ∨ ¬B *)
       | _ -> Not(simplify ~i:(i + 1) x))                                   (* ¬A ---> ¬A *)
    | Or (x,y) -> 
      (match (x,y) with
         _, And (b,c) -> And( Or(x,b), Or(x,c) )                            (* A ∨ (B ∧ C) ---> (A ∨ B) ∧ (A ∨ C) *)
       |And (a,b), _ -> And( Or(a,y), Or(b,y) )                             (* (A ∧ B) ∨ C ---> (A ∨ C) ∧ (B ∨ C) *)
       | (_,_) -> Or( (simplify ~i:(i + 1) x), (simplify ~i:(i + 1) y) ))   (* A ∨ B ---> A ∨ B *)
    | And (x,y) -> And( (simplify ~i:(i + 1) x), (simplify ~i:(i + 1) y) )  (* A ∧ B ---> A ∧ B *)
    | Implies (x,y) -> Or( Not(x), y)                                       (* A => B ---> ¬A ∨ B *)
    | Equivalent (x,y) -> And( Implies(x,y), Implies(y,x) )                 (*A <=> B ---> (A => B) ∧ (B => A) *) 
    | Forall (x,y) | Exists (x,y) -> skolem ~i expr in
  if expr = result then     
    result
  else
    simplify ~i:(i + 1) result;;

(*############################################################# CONVERSION TO CNF #############################################################*)

(* Recursively creates a clause (list of atoms) from an expression (Or, Not or Atom) *)
let rec to_clause expr =
  print_endline (String.concat "" ("To Clause: " :: string_of_expression expr :: []));  
  match expr with
    Or (x,y) -> List.rev_append (to_clause x) (to_clause y)
  | Not( Atom (x,y) ) -> [NegAtom (x,y)]
  | Atom (x,y) -> [PosAtom (x,y)]
  | _ -> []

(* Recursively creates cnf (list of clauses) from an expression (And) *)
let rec to_cnf expr =
  print_endline (String.concat "" ("To CNF:    " :: string_of_expression expr :: []));
  match expr with 
    And(x,y) -> List.rev_append (to_cnf x) (to_cnf y)
  | _ -> [to_clause expr];; 

(*############################################################# SOLVING #############################################################*)

(* Returns the cartesian product of two lists *)
let cartesian l l' = 
  List.concat (List.map (fun e -> List.map (fun e' -> (e, e')) l') l);;

(* Returns a list of all variables appearing in a given literal and it's sub-expressions (e.g. f(x,g(y)) => [x; y] *)
let rec vars_t literal =
  match literal with 
    Variable(x) -> Variable(x) :: []
  | Function(x, y) -> List.flatten (List.map vars_t y);;

(* Implements robinson's unification algorithm on a given set (list of pairs of literals) *)
let rec robinson_unify set = 
  match set with 
    [] -> true
  | h :: t -> match h with                                                                                                                              
      (Function(u, v), Function(x, y)) -> if (not (u = x) || (not ((List.length v) = (List.length y)))) then 
        (print_endline (String.concat "" ("Conflict: " :: string_of_literal (Function(u,v)) :: " and " :: string_of_literal (Function(x,y)) :: []));      (* conflict: G ∪ { f(s0,...,sk) ≐ g(t0,...,tm) } ⇒ ⊥	if f ≠ g or k ≠ m *)
         false)        
      else (print_endline (String.concat "" ("Decompose: " :: string_of_literal (Function(u,v)) :: " and " :: string_of_literal (Function(x,y)) :: []));  (* decompose: G ∪ { f(s0,...,sk) ≐ f(t0,...,tk) }	⇒	G ∪ { s0 ≐ t0, ..., sk ≐ tk }	*)
            (robinson_unify (List.append (List.combine v y) set)))
    | (Function(u, v), x) -> (print_endline (String.concat "" ("Swap: " :: string_of_literal (Function(u,v)) :: " and " :: string_of_literal x :: []));   (* swap: G ∪ { f(s0,...,sk) ≐ x }	⇒	G ∪ { x ≐ f(s0,...,sk) } *)
                              robinson_unify ((x, Function(u, v)) :: t))
    | (Variable(u), Function(x, y)) -> if (List.mem (Variable(u)) (vars_t (Function(x, y)))) then 
        (print_endline (String.concat "" ("Check: " :: string_of_literal (Variable(u)) :: " and " :: string_of_literal (Function(x, y)) :: []));          (* check: G ∪ { x ≐ f(s0,...,sk) } ⇒	⊥	if x ∈ vars(f(s0,...,sk))*)
         false) 
      else (print_endline (String.concat "" ("Eliminate: " :: string_of_literal (Variable(u)) :: " and " :: string_of_literal (Function(x, y)) :: []));   (* eliminate: G ∪ { x ≐ t } ⇒ G{x↦t} ∪ { x ≐ t }	if x ∉ vars(t) and x ∈ vars(G) *)
            false)
    | (x, y) -> print_endline (String.concat "" ("Delete: " :: string_of_literal x :: " and " :: string_of_literal y :: [])); robinson_unify t;;          (* delete: G ∪ { t ≐ t } ⇒ G *)

(* Attempts to unify two atoms by first checking that they are a positive and a negative instance of the same predicate, and then applying robinson's unification algorithm on them *)
let unify_atoms atom1 atom2 = 
  match (atom1, atom2) with 
    (NegAtom(u,v), PosAtom(x,y)) | 
    (PosAtom(u,v), NegAtom(x,y)) -> (print_endline (String.concat "" ("Unifying " :: string_of_atom atom1 :: " and " :: string_of_atom atom2 :: []))); 
    let result = (robinson_unify (List.combine v y)) in 
    if result then  
      (print_endline (String.concat "" ("Unified: " :: string_of_atom atom1 :: " and " :: string_of_atom atom2 :: [])); result)
    else
      (print_endline (String.concat "" ("Not unified: " :: string_of_atom atom1 :: " and " :: string_of_atom atom2 :: [])); result)
  | (x,y) -> false;;

(* Removes all occurences of a specific atom in the given list (clause) *)
let rec remove_atom l atom = 
  match l with 
    [] -> []
  | h :: t -> if h = atom then remove_atom t atom else h :: remove_atom t atom;;

(* Unifies two clauses (by unifying all their respective atoms) and generates a new clause: [] of no new clause, Empty if empty clause *)
let rec unify_clauses clause1 clause2 =
  if clause1 = clause2 then (print_endline (String.concat "" ("Skipping: " :: string_of_clause clause1 :: " and " :: string_of_clause clause2 :: " are equal." :: [])); clause1) else 
    match (clause1,clause2) with 
      ([], []) | ([], _) | (_, []) -> [False]
    | (_,_) ->
      let rec for_all pairs = 
        match pairs with
          [] -> []
        | (x, y) :: t -> let opposite x y = match (x,y) with 
              (NegAtom(m,n), PosAtom(u,v)) | (PosAtom(m,n), NegAtom(u,v)) -> if m = u then true else false
            | (_,_) -> false in  
          if (opposite x y) then 
            (if (unify_atoms x y) then 
               (unify_clauses (remove_atom clause1 x) (remove_atom clause2 y)) 
             else for_all t) 
          else for_all t in
      for_all (cartesian clause1 clause2);;

(* Applies Robinson's resolution algorithm to determine whether the formula is satisfiable. If it can generate an empty clause then the formula is invalid. Otherwise it is satisfiable. *)
let rec robinson_solve cnf = 
  let rec for_all pairs = 
    match pairs with
      [] -> true
    | (x, y) :: t -> print_endline (String.concat "" ("Testing:  " :: string_of_clause x :: " against " :: string_of_clause y :: [])); 
      let new_clause = unify_clauses x y in 
      match new_clause with
        [] -> for_all t
      | [False] -> false
      | _ -> if (new_clause = x) || (new_clause = y) then for_all t else for_all (List.append (List.map (fun e -> (e, new_clause)) cnf) t) in
  for_all (cartesian cnf cnf);;

(*############################################################# MAIN #############################################################*)

(* Calls all the necessary functions to solve expr. It's used to add some clarification text to the output *)
let solve expr = 
  print_endline (String.concat "" (String.make 1 '\n' :: "############### SIMPLIFYING ##############"  :: []));
  let simple = simplify expr in
  print_endline (String.concat "" ("Result: " :: string_of_expression simple :: []));
  print_endline (String.concat "" (String.make 1 '\n' :: "############ CONVERTING TO CNF ###########" :: []));
  let cnf = to_cnf simple in
  print_endline (String.concat "" ("Result: " :: string_of_cnf cnf :: []));
  print_endline (String.concat "" (String.make 1 '\n' :: "################# SOLVING ################" :: []));
  robinson_solve cnf;;

(* Main function *)
let main () =
  let x = Variable "x" in
  let y = Variable "y" in
  let z = Variable "z" in

  let a = Function ("a", []) in
  let b = Function ("b", []) in
  let c = Function ("c", []) in    

  let f = Not( Implies( Forall(x, Or( Atom("P", [x]), Atom("Q", [x]))), Or( Atom("P", [a]), Atom("Q", [a])))) in
  let f1 = Exists(x, Implies( Atom("P", [x]), And( Atom("P", [a]), Atom("P", [b])))) in  
  let f2 = Forall(x, Implies( Atom("P", [x]), Exists(y, Or( Atom("P", [y]), Atom("Q", [y]))))) in
  let f3 = Implies( Exists(x, Or( Atom("P", [x]), Atom("Q", [x]))), Or( Exists(x, Atom("P", [x])), Exists(x, Atom("Q", [x])))) in
  let f4 = Implies( And(Forall(x, Atom("P", [x])), Forall(x, Atom("Q", [x]))), Forall(x, And( Atom("P", [x]), Atom("Q", [x])))) in
  let f5 = Implies( Forall(x, And( Atom("P", [x]), Atom("Q", [x]))), And(Forall(x, Atom("P", [x])), Forall(x, Atom("Q", [x])))) in
  let f6 = Implies(Forall(x, Not( Atom("P", [x]))), Not( Exists(x, Atom("P", [x])))) in
  let f7 = Implies(Not( Forall(x, Atom("P", [x]))), Exists(x, Not( Atom("P", [x])))) in
  let f_test = f7 in
  print_endline (String.concat "" ("Is the formula " :: string_of_expression f_test :: " valid? " :: string_of_bool (not (solve (Not(f_test)))) :: []));; 

(* Top level, this should only contain a call to main () *)
main();;