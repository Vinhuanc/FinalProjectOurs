open Ast

module Parser = Parser
module Lexer = Lexer

let parse (s : string) : expression =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.expression_eof Lexer.token lexbuf in
     ast

let empty = []
let singleton x y = [(x,y)]

let rec append lst1 lst2 = 
  match lst1 with
  | [] -> lst2
  | h :: tl -> h :: append tl lst2

let merge s1 s2 =
    match s1, s2 with
    | [], [] -> None
    | [], _ -> Some s2
    | _, [] -> Some s1
    | _ , _ -> Some (append s1 s2)

let rec match_expression variables pattern expression =
    match pattern with
    | Identifier x ->
        if x = "x" then Some (singleton x expression)
            (*TODO: Fix test for variables, the string 
        "x" is not necessarily the only variable and it might not
        always be a variable either *)
        else(
            if pattern = expression then Some empty
            else None
        )
    | Application (p1, p2) ->
        (match expression with
        | Application (e1, e2) ->
            (match match_expression variables p1 e1, match_expression variables p2 e2 with
            | Some s1, Some s2 -> merge s2 s1
            | _ -> None)
        | _ -> None)
    | _ -> None

    let find x s = match s with
    | [] -> failwith "Not found (find was passed an empty list)"
    | [(k,v)] -> if x = k then v else failwith "Not found (find failed but the substitution being passed in really does not contain the variable)"
    | _ -> failwith "Find failed (key not found because this part of the find function is utterly broken)"
    
    let rec substitute variables s e = match e with
    | Identifier "x" -> find "x" s
    | Application (e1, e2) -> Application (substitute variables s e1, substitute variables s e2)
    | _ -> e

let rec string_of_pattern (p : pattern) : string =
  match p with
  | Constructor (name, []) -> name
  | Constructor (name, patterns) -> name ^ " (" ^ (String.concat ", " (List.map string_of_pattern patterns)) ^ ")"
  | Variable (name, type_name) -> name ^ " : " ^ type_name

let rec string_of_expression (e : expression) : string =
  match e with
  (* If you're confused about the structure of the AST,
     you can use this code to print more parentheses
     (besides using utop):
  | Application (Application (Identifier ",", e), arg) ->
    (string_of_expression_paren e) ^ ", " ^ (string_of_expression_paren arg)
  | Application (e, arg) ->
    (string_of_expression_paren e) ^ " " ^ string_of_expression_paren arg
     
     *)
  | Application (Application (Identifier ",", e), arg) ->
    (string_of_expression e) ^ ", " ^ (string_of_expression arg)
  | Application (e, arg) ->
    (string_of_expression e) ^ " " ^ string_of_expression_paren arg
  | Identifier name -> name
  | Match (e, cases) ->
    let case_strings = List.map (fun (pattern, body) ->
      let pattern_string = match pattern with
        | Constructor (name, []) -> name
        | Constructor (name, patterns) -> name ^ " (" ^ (String.concat ", " (List.map string_of_pattern patterns)) ^ ")"
        | Variable (name, type_name) -> name ^ " : " ^ type_name
      in
      (* the outer parentheses are redundant if the body does not end in a match, but better to be safe then sorry *)
      pattern_string ^ " -> " ^ (string_of_expression_paren body)
    ) cases in
    "match " ^ (string_of_expression e) ^ " with " ^ (String.concat " | " case_strings)

and string_of_expression_paren (e : expression) : string =
  match e with
  | Identifier name -> name
  | e -> "(" ^ string_of_expression e ^ ")"

let string_of_hint (h : hint option) : string =
  match h with
  | Some Axiom -> "\n(*hint: axiom *)"
  | Some (Induction name) -> "\n(*hint: induction " ^ name ^ " *)"
  | None -> ""
let string_of_equality (e : equality) : string =
  match e with
  | Equality (e1, e2) -> "(" ^ (string_of_expression e1) ^ " = " ^ (string_of_expression e2) ^ ")"
let string_of_typedvariable (TypedVariable (name, type_name) : typedVariable) : string =
  "(" ^ name ^ " : " ^ type_name ^ ")"
let string_of_declaration (d : declaration) : string =
  match d with
  | TypeDeclaration (name, variants) ->
    let variant_strings = List.map (function Variant (name, []) -> name
      | Variant (name, types) -> name ^ " of (" ^ (String.concat "*" types) ^ ")"
    ) variants in
    "type " ^ name ^ " = " ^ (String.concat " | " variant_strings)
  | FunctionDeclaration (TypedVariable (name, type_name), args, body) ->
    let arg_strings = List.map (function TypedVariable (name, type_name) -> "(" ^ name ^ " : " ^ type_name ^ ")") args in
    "let rec " ^ name ^ " " ^ (String.concat " " arg_strings) ^ " : " ^ type_name ^ " = " ^ (string_of_expression body)
  | ProofDeclaration (name, args, equality, hint) ->
    let arg_strings = List.map string_of_typedvariable args in
    "let (*prove*) " ^ name ^ " " ^ (String.concat " " arg_strings) ^ " = "
     ^ string_of_equality equality ^ string_of_hint hint

     let rec attempt_rewrite variables lhs rhs expression =
      match match_expression variables lhs expression with
        | Some s -> Some (substitute variables s rhs)
        | None -> (match expression with
            | Application (e1, e2) -> (match attempt_rewrite variables lhs rhs e2 with
                | None -> None (* todo: try the other side too! *)
                | Some e2' -> Some (Application (e1, e2')))
            | _ -> None (* not succesful *)
            )

            let rec perform_step rules expression = match rules with
            | (variables, nm, lhs, rhs) :: _ :: rest -> (match attempt_rewrite variables lhs rhs expression with
                | Some e -> Some (nm, e)
                | _ -> perform_step rest expression)
            | _ -> None       

            let rec perform_steps rules expression = match perform_step rules expression with
  | Some (nm, e) -> (nm, e) :: perform_steps [] e
  | None -> []

  let rec prove rules lhs rhs
  = string_of_expression lhs :: (* or Project2.string_of_expression ?? *)
    (match perform_steps rules lhs with
     | (nm, e) :: _ -> (" = { " ^ nm ^ " }") :: prove rules e rhs
     | [] -> if lhs = rhs then [] else " = { ??? }" :: [string_of_expression rhs]) (* or Project2.string_of_expression ?? *)

     let rec prover rules declarations =
      match declarations with
         | ProofDeclaration (nm, vars, Equality (lhs,rhs), None) :: rest
            -> (* no hint, so let's prove this *)
               prove rules lhs rhs :: prover ((vars,nm,lhs,rhs)::rules) rest
         | ProofDeclaration (nm, vars, Equality (lhs,rhs), _) :: rest
            -> (* we got a hint so we simply assume the statement *)
               prover ((vars,nm,lhs,rhs)::rules) rest
         | _ :: rest -> prover rules rest
         | [] -> []
   let prover_main decls =
      prover [] decls |>
      List.map (String.concat "\n") |>
      String.concat "\n\n" |>
      print_endline