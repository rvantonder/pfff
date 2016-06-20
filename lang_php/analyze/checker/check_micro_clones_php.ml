(** Using Ast_php and not Ast_php_simple for future proofing of
    automatic patching *)

module Ast = Ast_php
open Printf

let (!) = Export_ast_php.ml_pattern_string_of_expr
let str_of_tok tok = Parse_info.str_of_info tok

module Bexp : sig

  type symbol = Ast_php.expr * Ast_php.tok option (* parent tok *)
  type t =
    | Var of symbol
    | And of t list
    | Or  of t list
    | L_and of t list
    | L_or of t list
    | LL_and of t list
    | LL_or of t list

  val map_children : (t list -> t list) -> t -> t

  val apply_children : (t list -> 'b option) -> t -> 'b option

  val to_string : ?z3:bool -> t -> string
end = struct
  type symbol = Ast_php.expr * Ast_php.tok option
  type t =
    | Var of symbol
    | And of t list
    | Or  of t list
    | L_and of t list
    | L_or of t list
    | LL_and of t list
    | LL_or of t list


  let map_children (f: t list -> t list) (e : t) : t =
    match e with
    | And exps -> And (f exps)
    | Or exps -> Or (f exps)
    | L_or exps -> L_or (f exps)
    | L_and exps -> L_and (f exps)
    | LL_or exps -> LL_or (f exps)
    | LL_and exps -> LL_and (f exps)
    | x -> x

  let apply_children (f: t list -> 'b option) (e : t) : 'b option =
    match e with
    | And exps -> f exps
    | Or exps -> f exps
    | L_or exps -> f exps
    | L_and exps -> f exps
    | LL_or exps -> f exps
    | LL_and exps -> f exps
    | x -> None

  let to_string ?(z3=false) e =
    let open Printf in
    let rec to_string_exp =
      function
      | Or x -> sprintf "Or(%s)" @@ list_to_string x
      | And x -> sprintf "And(%s)" @@ list_to_string x
      | L_or x -> sprintf "Land(%s)" @@ list_to_string x
      | L_and x -> sprintf "Lor(%s)" @@ list_to_string x
      | LL_or x -> sprintf "LLor(%s)" @@ list_to_string x
      | LL_and x -> sprintf "LLand(%s)" @@ list_to_string x
      | Var (e,_) ->
        (match e with
         | Ast_php.IdVar (Ast_php.DName(v,_),_) ->
           if z3 then sprintf "B('%s')" v
           else sprintf "%s" v
         | x -> sprintf "%s" !x)
    and list_to_string (l : t list) : string =
      List.fold_left (fun (c,acc) x ->
          match c with
          | 0 -> (c+1),(to_string_exp x)
          | _ -> (c+1),(acc^", "^(to_string_exp x))) (0,"") l
      |> snd in
    to_string_exp e
end

let bool_exp_of_php_exp exp =
  let open Printf in
  let open Ast in
  let rec aux exp parent_tok =
    match exp with
    | Binary (lhs,(Logical OrBool,op_tok),rhs) ->
      Bexp.Or [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | Binary (lhs,(Logical AndBool,op_tok),rhs) ->
      Bexp.And [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | Binary (lhs,(Logical AndLog,op_tok),rhs) ->
      Bexp.L_and [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | Binary (lhs,(Logical OrLog,op_tok),rhs) ->
      Bexp.L_or [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | Binary (lhs,(Arith And,op_tok),rhs) ->
      Bexp.LL_and [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | Binary (lhs,(Arith Or,op_tok),rhs) ->
      Bexp.LL_or [aux lhs (Some op_tok); aux rhs (Some op_tok)]
    | ParenExpr (_,exp,_) as x ->
      (match parent_tok with
       | Some tok when str_of_tok tok = "||" ->
         Bexp.Or [aux exp parent_tok]
       | Some tok when str_of_tok tok = "&&" ->
         Bexp.And [aux exp parent_tok]
       | Some tok when str_of_tok tok = "and" ->
         Bexp.L_and [aux exp parent_tok]
       | Some tok when str_of_tok tok = "or" ->
         Bexp.L_or [aux exp parent_tok]
       | Some tok when str_of_tok tok = "|" ->
         Bexp.LL_or [aux exp parent_tok]
       | Some tok when str_of_tok tok = "&" ->
         Bexp.LL_and [aux exp parent_tok]
       | _ -> Bexp.Var (x,parent_tok))
    | x -> Bexp.Var (x,parent_tok)
  in aux exp None

open Bexp

let err_msg_of_tok tok =
  Parse_info.token_location_of_info tok
  |> fun info ->
  Printf.sprintf
    "%s:%d:%d" info.Parse_info.file
    info.Parse_info.line
    info.Parse_info.column

let flatten exp =
  let rec aux (exp : Bexp.t) : Bexp.t =
    match exp with
    | Or l -> flatten_exp l (Or [])
    | And l -> flatten_exp l (And [])
    | L_or l -> flatten_exp l (L_or [])
    | L_and l -> flatten_exp l (L_and [])
    | LL_or l -> flatten_exp l (LL_or [])
    | LL_and l -> flatten_exp l (LL_and [])
    | x -> x
  and
    flatten_exp l init =
    List.fold_right (fun x acc ->
        let res = aux x in
        match acc,res with
        | And l,And t -> And (t@l)
        | And l, x -> And (x::l)
        | Or l, Or t -> Or (t@l)
        | Or l, x -> Or (x::l)
        | L_or l, L_or t -> L_or (t@l)
        | L_or l, x -> L_or (x::l)
        | L_and l, L_and t -> L_and (t@l)
        | L_and l, x -> L_and (x::l)
        | LL_or l, LL_or t -> LL_or (t@l)
        | LL_or l, x -> LL_or (x::l)
        | LL_and l, LL_and t -> LL_and (t@l)
        | LL_and l, x -> LL_and (x::l)
        | _,x -> x) l init
  in aux exp

let print_rewrite rule exp exp' =
  printf "\t[+] Rule: %s %s -> %s\n" rule (to_string exp) (to_string exp')

(** Find the first var and use that. [v] is for the actual statement *)
let print_error ?(v=false) exp =
  let res  =
    let rec aux = function
      | Var x -> Some x
      | And (hd::_) -> aux hd
      | Or (hd::_) -> aux hd
      | L_and (hd::_) -> aux hd
      | L_or (hd::_) -> aux hd
      | LL_and (hd::_) -> aux hd
      | LL_or (hd::_) -> aux hd
      | _ -> None
    in aux exp in
  match res with
  | Some (dup_var,Some parent_tok) ->
    let err_msg = err_msg_of_tok parent_tok in
    let err_tok = str_of_tok parent_tok in
    if v then printf " %s:%s:%s\n%!" err_tok err_msg !dup_var
    else printf " %s:%s\n%!" err_tok err_msg
  | _ -> ()

let compare exp1 exp2 =
  String.compare (Bexp.to_string exp1) (Bexp.to_string exp2)

(**
   Or([Var "a"; Var "b"; Var "a"]) -> Or([Var "a"; Var "b"])
*)
let rule_dedup ?(v=true) exp =
  let (!) = to_string in
  let dedup l =
    List.fold_right (fun x acc ->
        if List.exists (fun y -> !x = !y) acc
        then (print_error x;
              acc) else x::acc) l [] in
  Bexp.map_children dedup exp

(**
   Unbox if there is only one expression in the list of a bool exp
   Or([And([Var "b";Var "c"])]) -> And([Var "b"; Var "c"])
   Or([Var x]) -> Var x

   Bexp.apply_children (fun l ->
      match l with
      | (x::[]) -> Some x
      | x -> None) exp
   |> function
   | Some res -> res
   | None -> exp
*)
let rule_simple ?(v=false) =
  function
  | Or (x::[]) -> x
  | And (x::[]) -> x
  | L_or (x::[]) -> x
  | L_and (x::[]) -> x
  | LL_or (x::[]) -> x
  | LL_and (x::[]) -> x
  | x -> x

let rewrite exp =
  let rec aux exp =
    match exp with
    | And x ->
      let res = List.map aux x in
      And res |> rule_dedup |> rule_simple
    | Or x ->
      let res = List.map aux x in
      Or res |> rule_dedup |> rule_simple
    | L_or x ->
      let res = List.map aux x in
      L_or res |> rule_dedup |> rule_simple
    | L_and x ->
      let res = List.map aux x in
      L_and res |> rule_dedup |> rule_simple
    | LL_or x ->
      let res = List.map aux x in
      LL_or res |> rule_dedup |> rule_simple
    | LL_and x ->
      let res = List.map aux x in
      LL_and res |> rule_dedup |> rule_simple
    | x -> x in
  aux exp

let simplify ?(v=false) exp =
  let bexp = bool_exp_of_php_exp exp in
  if v then
    (printf "\n[+] Exp:\n%!";
     printf "%s\n%!" @@ to_string ~z3:true bexp;
     printf "%s\n%!" @@ to_string bexp);
  let flat_exp = flatten bexp in
  if v then
    (printf "[+] Flat:\n%!";
     printf "%s\n%!" @@ to_string flat_exp);
  let simple = rewrite flat_exp in
  if v then
    (printf "[+] Simpl:\n%!";
     printf "%s\n%!" @@ to_string simple)

let check ast =
  let open Ast in
  let visitor = Visitor_php.mk_visitor {
      Visitor_php.default_visitor with
      Visitor_php.kexpr = (fun (k,_) e ->
          match e with
          | Ast_php.Sc sc -> ()
          | _ -> k e);

      Visitor_php.kstmt = (fun (k,_) s ->
          match s with
          | If (if_tok,(_,cond_exp,_),_,elseifs,_) ->
            let exps =
              cond_exp::(List.map (fun ((_,(_,exp,_),_)) -> exp) elseifs)
            in
            List.iter simplify exps;
            k s
          | _ -> k s)
    } in
  visitor (Ast.Program ast)
