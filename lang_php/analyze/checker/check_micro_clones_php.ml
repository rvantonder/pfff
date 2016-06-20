(** Using Ast_php and not Ast_php_simple for future proofing of
    automatic patching *)

module Ast = Ast_php
open Printf

let (!) = Export_ast_php.ml_pattern_string_of_expr
let str_of_tok tok = Parse_info.str_of_info tok

module Boolean : sig
  type op = And | Or

  type 'a t = private
    | Atom of 'a
    | List of op * 'a t list

  val make : op -> 'a t -> 'a t -> 'a t

  module Lang : sig
    val (||) : 'a t -> 'a t -> 'a t
    val (&&) : 'a t -> 'a t -> 'a t
    val v : 'a -> 'a t
  end
end = struct
  type op = And | Or
  type 'a t =
    | Atom of 'a
    | List of op * 'a t list

  let make op x y =
    match x,y with
    | List (op1,xs), List (op2,ys) when op1 = op && op2 = op ->
      List (op, xs@ys)
    | _,List (op2,ys) when op2 = op ->
      List (op,x::ys)
    | List (op1,xs),_ when op1 = op ->
      List (op,xs@[y])
    | x,y ->
      List (op,[x;y])

  module Lang = struct
    let (||) op1 op2 = make Or op1 op2
    let (&&) op1 op2 = make And op1 op2
    let v x = Atom x
  end
end

type s = Ast_php.expr * Ast_php.tok option

open Boolean

let op_to_string = function
  | And -> "And"
  | Or -> "Or"

let to_string exp =
  let (!) = Export_ast_php.ml_pattern_string_of_expr in
  let rec exp_to_string =
    function
    | Atom (Ast_php.IdVar (Ast_php.DName(v,_),_),_) -> sprintf "%s" v
    | Atom (x,_) -> !x
    | List (op,l)
      -> sprintf "%s(%s)" (op_to_string op) (list_to_string l)
  and
    list_to_string (l : s t list) : string =
    List.fold_left (fun (c,acc) x ->
        match c with
        | 0 -> (c+1),(exp_to_string x)
        | _ -> (c+1),(acc^", "^(exp_to_string x))) (0,"") l |> snd
  in
  exp_to_string exp

(** create a Boolean.t expression from an AST expression *)
let bool_exp_of_php_exp exp : s Boolean.t =
  let open Printf in
  let open Ast in
  let rec aux exp parent_tok : s Boolean.t =
    match exp with
    | Binary (lhs,(Logical OrBool,op_tok),rhs) ->
      Boolean.Lang.(aux lhs (Some op_tok) || aux rhs (Some op_tok))
    | Binary (lhs,(Logical AndBool,op_tok),rhs) ->
      Boolean.Lang.(aux lhs (Some op_tok) && aux rhs (Some op_tok))
    | ParenExpr (_,exp,_) -> aux exp parent_tok
    | x -> Boolean.Lang.v (x, parent_tok)
  in aux exp None

let err_msg_of_tok tok =
  Parse_info.token_location_of_info tok
  |> fun info ->
  Printf.sprintf
    "%s:%d:%d" info.Parse_info.file
    info.Parse_info.line
    info.Parse_info.column

(** Find the first var and use that. [v] is for the actual statement *)
let print_error ?(v=false) exp =
  let res  =
    let rec aux = function
      | Atom x -> Some x
      | List (_,hd::_) -> aux hd
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
  String.compare (to_string exp1) (to_string exp2)

let dedup l =
  List.fold_left (fun acc x ->
      if List.exists (fun y -> compare x y = 0) acc
      then (print_error x; acc) else x::acc) [] l |> List.rev

let boolean_of_list op (l : s Boolean.t list) : s Boolean.t =
  let rec aux l =
    match l with
    | [Atom x] -> Lang.v x
    | x::y::[] -> make op x y
    | hd::tl  -> make op hd (aux tl)
    | [] -> failwith "Error: empty list. Invariant broken."
  in aux l

let rule_dedup (exp : s Boolean.t) : s Boolean.t =
  match exp with
  | List (op,l) -> dedup l |> boolean_of_list op
  | Atom x -> Lang.v x

let bur_map f (exp : s Boolean.t) : s Boolean.t =
  let rec aux exp =
    match exp with
    | List (op,l) ->
      let e = List.map aux l |> boolean_of_list op in
      f e
    | x -> f x in
  aux exp

let simplify ?(v=false) exp =
  let exp' = bool_exp_of_php_exp exp in
  if v then
    (printf "\n[+] Exp:\n%!";
     printf "%s\n%!" @@ to_string exp');
  let exp'' = bur_map rule_dedup exp' in
  if v then
    (printf "\n[+] Exp':\n%!";
     printf "%s\n%!" @@ to_string exp'')

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
