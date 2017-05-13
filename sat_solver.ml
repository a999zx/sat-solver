
(*
 * SAT Solver
 * 入力形式はDIAMACS形式
 *
 * c
 * c <comments>
 * ...
 * c
 * p cnf N M
 * 13 -4 5 0
 * 4 5 1 0
 * ...
 * 
 * (N:変数の数 M:節の数)
 *)

open Scanf

type value = True | False | Unknown
type lit = int
type clause = lit list
type c_set = clause list
           
(*
 * リストlから要素eを探し出し、eがある位置を返す。
 * eがない場合は、例外Not_foundを返す。
 *)
let find_element e l =
  let rec fe_sub e1 l1 n =
    match l1 with
    | [] -> raise Not_found
    | x :: xs -> if x = e1 then n
                 else fe_sub e1 xs (n + 1)
  in fe_sub e l 0

   
(* リストlから要素eを全て削除したリストを返す。 *)
let rec remove_element e l =
  match l with
  | [] -> []
  | x :: xs -> if x = e then remove_element e xs
               else x :: (remove_element e xs)

                                   
(* リストが空かどうか *)
let is_empty = function
  | [] -> true
  | _ -> false

       
(* 節集合の中で一番短い節を探し、何番目かを返す *)
let find_min_length_c_set (cs : c_set) =
  let rec fmlcs_sub cs1 min i = 
    match cs1 with
    | [] -> min
    | s :: ss -> if List.length (List.nth cs min) > List.length s
                 then fmlcs_sub ss i (i + 1)
                 else fmlcs_sub ss min (i + 1)
  in fmlcs_sub (List.tl cs) 0 1
  
  
       
(*
 * リテラルlを真としたときのlの除去
 * lを含む節を除去し、節の中の-lを消去する。
 *)
let rec remove_literal (l : lit) (cs : c_set) : c_set =
  match cs with
  | [] -> []
  | s :: ss -> if List.mem l s then remove_literal l ss
               else (remove_element (-l) s) :: (remove_literal l ss)
       
       
(* 
 * 1リテラル規則
 * 節集合c_setに1リテラル規則を適用した結果の節集合を返す。
 * find_one_literalにおいて1リテラルしかない節があるかどうかを探し、あった場合はその
 * リテラルを返す。見つからない場合は例外Not_foundを返す。
 * 1リテラルしかない節が見つかったときは、そのリテラルについて節集合に1リテラル規則を
 * 適用し、適用後の節集合に再帰的にone_literal_ruleを適用する。
 * find_one_literalが例外を返した場合は、1リテラル規則が適用できないので、節集合を
 * そのまま返す。
 *)
let rec one_literal_rule (cs : c_set) (values : value array) : c_set * value array =
  let rec find_one_literal cs1 =
    match cs1 with
    | [] -> raise Not_found
    | s :: ss -> if List.length s = 1 then List.hd s
                 else find_one_literal ss
  in
  try
    let tmpl = find_one_literal cs in
    if tmpl > 0 then Array.set values (tmpl - 1) True
    else Array.set values ((abs tmpl) - 1) False;
    one_literal_rule (remove_literal tmpl cs) values
  with _ -> (cs, values)
                
                
(* 
 * DPLLアルゴリズム
 * 分割規則を適用する変数は、節集合の初めの節の初めの要素としている。
 *)
let rec dpll (cs : c_set) n (values : value array) : bool =
  let (cs1, values1) = one_literal_rule cs values in    (* 1リテラル規則適用 *)
  if is_empty cs1 then true    (* 節集合が空ならtrue *)
  else if List.exists is_empty cs1 then false    (* 空である節が存在する場合はfalse *)
  else
    let tmpl = abs (List.hd (List.nth cs1 (find_min_length_c_set cs1))) in
    Array.set values1 (tmpl - 1) True;
    if dpll (remove_literal tmpl cs1) n values1 then true
    else
      (Array.set values1 (tmpl - 1) False;
       if dpll (remove_literal (-tmpl) cs1) n values1 then true
       else (Array.set values1 (tmpl - 1) Unknown;
             false))

(* 空白区切りで文字列を読み込む *)
let read_string_split_space () =
  bscanf Scanning.stdin " %s" (fun x -> x)
    
(* 空白区切りで整数を読み込む *)
let read_int_split_space () =
  bscanf Scanning.stdin " %d" (fun x -> x)
  
(*
 * 標準入力からm個の節を読み込み、節集合を作る。
 * 入力が有効な変数かどうかを判定するために、変数の数も引数として受け取る。
 * 入力された数字がnより大きい場合はエラー。
 *)
let make_c_set n m : c_set=
  let rec mcs_sub m1 s_set =
    let rec make_section s =
      let tmp = scanf " %d" (fun x -> x) in
      if tmp > n then failwith "invalid_variable"
      else if tmp = 0 then s
      else make_section (tmp::s)      
    in
    if m1 = 0 then s_set
    else mcs_sub (m1 - 1) ((make_section []) :: s_set)
  in mcs_sub m []

let rec print_values (values : value array) =
  let print i v =
    print_int (i + 1); print_string ": ";
    match v with
    | True -> print_string "True\n"
    | False -> print_string "False\n"
    | Unknown -> print_string "Unknown\n"
  in
  Array.iteri print values
   
(* 変数n個の分の真理値を記録したリストを返す。最初は全てUnknown。 *)   
let main () =
  let rec read_cnf () =
    let line = Str.split (Str.regexp "[ \t]+") (read_line ()) in
    if is_empty line then read_cnf ()
    else
      match List.hd line with
      | "c" -> read_cnf ()
      | "p" ->
         begin
           match List.nth line 1 with
           | "cnf" ->
              let n = int_of_string (List.nth line 2) in
              let m = int_of_string (List.nth line 3) in
              let expr = make_c_set n m in
              let values = Array.make n Unknown in
              let b = dpll expr n values in
              if b then (print_string "SAT\n"; print_values values)
              else print_string "UNSAT\n"
           | _ -> failwith "invalid format"
         end
      | _ -> failwith "invalid format"
  in read_cnf ()
           
let () =
  main ()
