(* hw1.ml
 * Handling infix expressions with percents:
 *
 *   x + y %
 *   x - y %
 *   x * y %
 *
 * Programmer: Mayer Goldberg, 2024
 *)


 type binop = Add | Sub | Mul | Div | Mod | Pow | AddPer | SubPer | PerOf;;
 
 type expr =
   | Num of int
   | Var of string
   | BinOp of binop * expr * expr
   | Deref of expr * expr
   | Call of expr * expr list;;
 
 type args_or_index = Args of expr list | Index of expr;;
 
 module type INFIX_PARSER = sig
   val nt_expr : expr PC.parser
 end;; (* module type INFIX_PARSER *)
 
 module InfixParser : INFIX_PARSER = struct
   open PC;;
 
   (* Parse whitespace and skip *)
   let nt_whitespace = const (fun ch -> ch <= ' ');;
   let make_space nt =
     let nt1 = star nt_whitespace in
     let nt1 = pack (caten nt1 (caten nt nt1)) (fun (_, (e, _)) -> e) in
     nt1;;
 
   (* Parse integers *)
   let nt_num =
     let nt1 = plus (range '0' '9') in
     let nt1 = pack nt1 (fun digits ->
       int_of_string (String.concat "" (List.map (String.make 1) digits))) in
     let nt1 = make_space nt1 in
     let nt1 = disj
       (pack (caten (char '-') nt1) (fun (_, n) -> -n))
       nt1 in
     nt1;;
 
   (* Parse variables *)
   let nt_var =
     let nt_start = range_ci 'a' 'z' in
     let nt_rest = disj_list [range_ci 'a' 'z'; range '0' '9'; one_of "$_"] in
     let nt1 = caten nt_start (star nt_rest) in
     let nt1 = pack nt1 (fun (first, rest) ->
       String.concat "" ((String.make 1 first) :: List.map (String.make 1) rest)) in
     let nt1 = only_if nt1 (fun str -> str <> "mod") in
     make_space nt1;;
 
   (* Parse parentheses or brackets *)
   let make_nt_parn par_left par_right nt =
     let nt1 = make_space (char par_left) in
     let nt2 = make_space (char par_right) in
     let nt1 = caten nt1 (caten nt nt2) in
     let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
     nt1;;
 
   (* Parse function calls or array access *)
   let nt_args_or_index nt_expr =
     let nt_args =
       let nt1 = make_nt_parn '(' ')' (star (caten nt_expr (maybe (char ',')))) in
       pack nt1 (fun exprs -> Args (List.map fst exprs)) in
     let nt_index =
       let nt1 = make_nt_parn '[' ']' nt_expr in
       pack nt1 (fun expr -> Index expr) in
     disj nt_args nt_index;;
 
   let nt_call_or_deref nt_expr =
     let nt1 = caten nt_var (star (nt_args_or_index nt_expr)) in
     let nt1 = pack nt1 (fun (func_or_arr, args_or_indices) ->
       let initial_expr = Var func_or_arr in
       List.fold_left
         (fun acc next ->
            match next with
            | Args args -> Call (acc, args)
            | Index index -> Deref (acc, index))
         initial_expr
         args_or_indices) in
     nt1;;
 
   (* Recursive parsing for expressions *)
   let rec nt_expr str = nt_add_sub_expr str
   and nt_add_sub_expr str =
     let nt1 = disj (pack (char '+') (fun _ -> Add)) (pack (char '-') (fun _ -> Sub)) in
     let nt1 = caten nt1 nt_mul_div_mod_expr in
     let nt1 = not_followed_by nt1 (char '%') in
     let nt1 = star nt1 in
     let nt1 = caten nt_mul_div_mod_expr nt1 in
     let nt1 = pack nt1 (fun (e, op_e_s) ->
       List.fold_left
         (fun acc -> function
           | (Add, e') -> BinOp (Add, acc, e')
           | (Sub, e') -> BinOp (Sub, acc, e')
           | _ -> failwith "Unexpected operator in nt_add_sub_expr")
         e
         op_e_s) in
     make_space nt1 str
   and nt_mul_div_mod_expr str =
     let nt1 = disj_list [pack (char '*') (fun _ -> Mul); pack (char '/') (fun _ -> Div); pack (word "mod") (fun _ -> Mod)] in
     let nt1 = caten nt1 nt_percent_expr in
     let nt1 = not_followed_by nt1 (char '%') in
     let nt1 = star nt1 in
     let nt1 = caten nt_percent_expr nt1 in
     let nt1 = pack nt1 (fun (e, op_e_s) ->
       List.fold_left
         (fun acc -> function
           | (Mul, e') -> BinOp (Mul, acc, e')
           | (Div, e') -> BinOp (Div, acc, e')
           | (Mod, e') -> BinOp (Mod, acc, e')
           | _ -> failwith "Unexpected operator in nt_mul_div_mod_expr")

         e
         op_e_s) in
     make_space nt1 str
   and nt_percent_expr str =
     let nt1 = caten (make_space (pack (char '*') (fun _ -> Mul))) (caten nt_add_sub_percent_expr (make_space (char '%'))) in
     let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
     let nt1 = caten nt_add_sub_percent_expr (star nt1) in
     let nt1 = pack nt1 (fun (e, es) ->
       List.fold_left
         (fun acc e' -> BinOp (PerOf, acc, e'))
          e
          es) in
     make_space nt1 str

  and nt_add_sub_percent_expr str =
     let nt1 = caten (disj (make_space (pack (char '+') (fun _ -> Add))) (make_space (pack (char '-') (fun _ -> Sub))))
                  (caten nt_power_expr (make_space (char '%'))) in
     let nt1 = pack nt1 (fun (op, (e, _)) -> (op, e)) in
     let nt1 = caten nt_power_expr (star nt1) in
     let nt1 = pack nt1 (fun (e, op_e_s) ->
    List.fold_left
      (fun acc -> function
        | (Add, e') -> BinOp (AddPer, acc, e')
        | (Sub, e') -> BinOp (SubPer, acc, e')
        | _ -> failwith "Unexpected operator in nt_add_sub_percent_expr")
      
      e
      op_e_s) in
  make_space nt1 str


   and nt_power_expr str =
     let nt1 = caten (pack (char '^') (fun _ -> Pow)) nt_func_call_array_index_expr in
     let nt1 = pack nt1 (fun (_, e) -> e) in
     let nt1 = caten nt_func_call_array_index_expr (star nt1) in
     let nt1 = pack nt1 (fun (e, es) -> e :: es) in
     let nt1 = pack nt1 List.rev in
     let nt1 = pack nt1 (function
       | e :: es ->
         List.fold_left
           (fun acc e' -> BinOp (Pow,  e', acc))
           e
           es
       | [] -> raise (PC.X_no_match)) in
     make_space nt1 str
and nt_func_call_array_index_expr str =
  let nt_args =
    let nt1 = star (caten nt_expr (maybe (make_space (char ',')))) in
    let nt1 = pack nt1 (fun exprs -> List.map fst exprs) in
    let nt1 = caten (make_space (char '(')) (caten nt1 (make_space (char ')'))) in
    let nt1 = pack nt1 (fun (_, (es, _)) -> Args es) in
    nt1 in
  
  let nt_index =
    let nt1 = caten (make_space (char '[')) (caten nt_expr (make_space (char ']'))) in
    let nt1 = pack nt1 (fun (_, (e, _)) -> Index e) in
    nt1 in
  
  let nt1 = disj nt_args nt_index in
  let nt1 = star nt1 in
  
  let nt1 = caten nt_basic_expr nt1 in
  let nt1 = pack nt1 (fun (e, s) ->
    List.fold_left
      (fun acc -> function
        | Args es -> Call (acc, es)
        | Index e' -> Deref (acc, e'))
      e
      s) in
  
  make_space nt1 str

and nt_basic_expr str =
  let nt1 = pack nt_num (fun n -> Num n) in
  let nt2 = pack nt_var (fun s -> Var s) in
  let nt1 = disj nt1 nt2 in
  let nt2 = make_nt_parn '(' ')' nt_expr in
  let nt1 = disj nt1 nt2 in
  let nt2 = make_nt_parn '(' ')' (caten (char '-') nt_expr) in
  let nt2 = pack nt2 (fun (_, e) -> BinOp (Sub, Num 0, e)) in
  let nt1 = disj nt1 nt2 in
  let nt2 = make_nt_parn '(' ')' (caten (char '/') nt_expr) in
  let nt2 = pack nt2 (fun (_, e) -> BinOp (Div, Num 1, e)) in
  let nt1 = disj nt1 nt2 in
  nt1 str;;
 end;;
 
 open InfixParser;;