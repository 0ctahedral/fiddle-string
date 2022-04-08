open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors

let t name program input expected = name>::test_run ~args:[] ~std_input:input program name expected;;
let ta name program input expected = name>::test_run_anf ~args:[] ~std_input:input program name expected;;
let tgc name heap_size program input expected = name>::test_run ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let tvg name program input expected = name>::test_run_valgrind ~args:[] ~std_input:input program name expected;;
let tvgc name heap_size program input expected = name>::test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let terr name program input expected = name>::test_err ~args:[] ~std_input:input program name expected;;
let tgcerr name heap_size program input expected = name>::test_err ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let tanf name program _input expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let tparse name program expected = name>::fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

(*let tfvs name program expected = name>::
  (fun _ -> 
    let ast = parse_string name program in 
    let anfed = anf (tag ast) in 
    let vars = free_vars_P anfed [] in 
    let c = Stdlib.compare in 
    let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in 
    assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print) 
;; *)

let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    match anfed with
    | AProgram(body, _) ->
      let vars = free_vars body in
      let c = Stdlib.compare in
      let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
      assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print)
;;

let fv_tests = [
  tfvs "num_bool" "5 == true" [];
  tfvs "x" "x" ["x"];
  tfvs "let_x" "let x = 5 in x" [];
  tfvs "let_x_y" "let x = 5 in y" ["y"];
  tfvs "fv_let2" "let x = y, z = h in x + z" ["y"; "h"];
  tfvs "fv_lambda" "(lambda(x): x * y)" ["y";];
  tfvs "fv_lambda_some_args" "(lambda(a, b): a + b)" [];
  tfvs "fv_letrec" "let rec fact =
        (lambda(n):
          if n == x: 1 else: n * fact(n - 1)) in fact(3) + y
" ["x"; "y"];
];;

let builtins_size = 4 (* arity + 0 vars + codeptr + padding *) * (List.length Compile.native_fun_bindings)

let simple_tests = [
  t "five" "5" "" "5";
  t "simple_let" "let x = 5 in x" "" "5";
  t "simple_prim1" "let x = 5 in add1(x)" "" "6";
  t "simple_prim2" "let x = 3, y = x + 5 in y * 2" "" "16";
]

let program_tests = [
  t "simple" "let x = 5 in x" "" "5";
  t "number5" "5" "" "5";
  t "tuple" "let t = (0, 5) in t" "" "(0, 5)";
  t "tuple_simple" "let a = (1, 2) in let b = (3, 4) in (5, 6)" "" "(5, 6)";
  t "thruple" "let t = (0, 3, 5) in t" "" "(0, 3, 5)";
  t "thruple_get" "let t = (0, 3, 5) in t[0]" "" "0";
  terr "too_high" "let t = (0, 3, 5) in t[7]" "" "index too large to get, got 7";
  terr "too_low" "let t = (0, 3, 5) in t[-3]" "" "index too small to get, got -3";

  t "nil" "let t = nil in t" "" "nil";
  terr "deref_nil" "let t = nil in t[0]" "" "tried to access component of nil";

  t "set" "let t = (0, 3) in t[0] := 10" "" "10";
  t "set_confirm" "let t = (0, 3) in let x = t[0] := 10 in t" "" "(10, 3)";
  t "set_get" "let t = (0, 3) in let x = t[0] := 10 in t[0]" "" "10";

  t "blank" "let _ = print((0, 2 + 1)) in 5" "" "(0, 3)\n5";

  t "nested" "let t = (0, (2, 1)) in t" "" "(0, (2, 1))";
  t "double_nested" "let t = ((2, 1), (4, 5)) in t" "" "((2, 1), (4, 5))";

  t"desugar_bindlist" "let (a, b, c) = (0, 3, 5) in c" "" "5";
  t"bindlist_destructure_nested" "let (a, (b, c)) = (0, (3, 5)) in (a, b, c)" "" "(0, 3, 5)";
  t"bindlist_keep_structure" "let (a, b) = (0, (3, 5)) in b" "" "(3, 5)";
  t "eq1" "nil == nil" "" "true";
  t "eq2" "nil == ()" "" "false";
  t "eq3" "() == ()" "" "false";
  t "eq4" "true == (3, 4)" "" "false";
  t "let" "let x = 5, y = 6 in let z = 10 in x * y + z" "" "40";
  t "tuples_let" "let t = (1, 2) in let (a, b) = t, m = 3 in a + (b * m)" "" "7";
  t "closure_test" "
    let p = 7,
        q = 3,
        f = (lambda (x): 
                let g = p + q in
                x * g) in
    let t = (1, 20) in
f(f((0, 1)[1]))" "" "100";
  t "curry_test" "
let addx = (lambda (x): (lambda (y): x + y)),
    z = 5 
in
let f = addx(z)
in
f(6)
  " "" "11";
  t "stack_alloc1" "let x = 5 in let y = 6 in let z = y in let f = (lambda: x + z) in let h = (lambda: z + y) in f()" "" "11";
  t "stack_alloc2" "let a = 1, b = 2, c = 3, d = 4, e = 5 in let f = (lambda: a + e) in f()" "" "6";
  t "tuple_eq1" "equal((1,), ())" "" "false";
  t "tuple_eq2" "equal((1, (2, 3), 4), (1, (2, 3), 4))" "" "true";
  t "tuple_eq3" "equal((1, (2, (3, 4))), (1, (2, (3, 4))))" "" "true";
  t "tuple_eq4" "equal((1, (2, 3)), (1, 2, 3))" "" "false";
  t "tuple_eq" "equal((1, 2), (1, 2))" "" "true";
  t "tuple_eq5" "equal((1, nil, 3), (1, nil, 3))" "" "true";

  t "fact" "let rec fact =
        (lambda(n):
          if n == 0: 1 else: n * fact(n - 1)) in fact(3)" "" "6";
  t "mutate_closed" "
  let t = (1, 2, 3),
  f = (lambda (n, x): t[n] := x) in
  begin
    f(0, 3);
    f(1, (4, 5));
    f(2, nil);
    t
  end
  " "" "(3, (4, 5), nil)";

  t "tambda" "
    let t = ((lambda: 10), (lambda (y): y)) in
    (t[0](), t[1](1))
  " "" "(10, 1)";
];; 

let type_tests = [ 
  t "isbool_true" "isbool(true)" "" "true";
  t "isbool_false" "isbool(false)" "" "true";
  t "isbool_num" "isbool(5)" "" "false";
  t "isbool_tuple" "isbool((5, 3))" "" "false";
  t "isbool_nil" "isbool(nil)" "" "false";
  t "isbool_empty" "isbool(())" "" "false";

  t "istuple_nil" "istuple(nil)" "" "true";
  t "istuple_empty" "istuple(())" "" "true";
  t "istuple_tuple" "istuple((5, 3))" "" "true";
  t "istuple_num" "istuple(5)" "" "false";
  t "istuple_true" "istuple(true)" "" "false";
  t "istuple_false" "istuple(false)" "" "false";

  t "isnum_nil" "isnum(nil)" "" "false";
  t "isnum_num" "isnum(5)" "" "true";
  t "isnum_true" "isnum(true)" "" "false";
  t "isnum_false" "isnum(false)" "" "false";
  t "isnum_tuple" "isnum((5, 3))" "" "false"; 

  t "test_is_bool2" "isbool(false)" "" "true";
  t "test_is_bool3" "isbool(0)" "" "false";
  t "test_is_bool4" "isbool(123)" "" "false";
  t "test_is_bool5" "isbool((0,123))" "" "false";
  t "test_is_bool6" "isbool((true,123))" "" "false";
  t "test_is_bool7" "isbool((123,123))" "" "false";
  t "test_is_bool8" "isbool((false,123))" "" "false";

  t "test_is_tuple1" "istuple(true)" "" "false";
  t "test_is_tuple2" "istuple(false)" "" "false";
  t "test_is_tuple3" "istuple(0)" "" "false";
  t "test_is_tuple4" "istuple(123)" "" "false";
  t "test_is_tuple5" "istuple((0,123))" "" "true";
  t "test_is_tuple6" "istuple((true,123))" "" "true";
  t "test_is_tuple7" "istuple((123,123))" "" "true";
  t "test_is_tuple8" "istuple((false,123))" "" "true";

  t "test_is_num1" "isnum(true)" "" "false";
  t "test_is_num2" "isnum(false)" "" "false";
  t "test_is_num3" "isnum(0)" "" "true";
  t "test_is_num4" "isnum(123)" "" "true";
  t "test_is_num5" "isnum((0,123))" "" "false";
  t "test_is_num6" "isnum((true,123))" "" "false";
  t "test_is_num7" "isnum((123,123))" "" "false";
  t "test_is_num8" "isnum((false,123))" "" "false";
];;

let pair_tests = [
  t "tup1" "let t = (4, (5, 6)) in
            begin
              t[0] := 7;
              t
            end" "" "(7, (5, 6))";
  t "tup2" "let t = (4, (5, nil)) in
            begin
              t[1] := nil;
              t
            end" "" "(4, nil)";
  t "tup3" "let t = (4, (5, nil)) in
            begin
              t[1] := t;
              t
            end" "" "(4, <cyclic tuple 1>)";
  t "tup5" "let t = (4, (5, (6, nil))) in
            begin
              t[1][1][1] := t;
              t
            end" "" "(4, (5, (6, <cyclic tuple 1>)))";
  t "tup4" "let t = (4, 6) in
            (t, t)"
           ""
           "((4, 6), (4, 6))";

  terr "tup_get_not_num" "let x = (1, 2, 3) in let y = (0, 6) in x[y]" "" "expected numeric index";
];;

let oom = [
  tgcerr "oomgc1" (0 + builtins_size) "(1, (3, 4))" "" "Out of memory";
  tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
  tgcerr "oomgc5" (builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation";
  tgcerr "oomg_tup1" (0 + builtins_size)
    "let t = ((1, 2, 3, 4, 5, 6, 7), 5) in
        begin
          t[0] := 4;
          t[0] := (7, 6, 5, 4, 3, 2, 1);
          t
        end"
        ""
        "Out of memory"
]

let gc = [
  tgc "gc_lam1" (10 + builtins_size)
      "let f = (lambda: (1, 2)) in
       begin
         f();
         f();
         f();
         f()
       end"
      ""
      "(1, 2)";

 tgc "gc_tup1" (10 + builtins_size)
      "let t = (1, 5),
        _ = (1, 2, 3, 4, 5, 6, 7),
        _ = (7, 6, 5, 4, 3, 2, 1) in 
        begin
          t[0] := (7, 6, 5, 4, 3, 2, 1);
          t
        end
      "
      ""
      "((7, 6, 5, 4, 3, 2, 1), 5)";

 tgc "gc_lambda" (7 + builtins_size)
 "let b = 5 in
  let rec f = (lambda (x): (1 + b, x)) in
    begin
      f(1);
      f(2);
      f(3);
      f(4)
    end
  "
 ""
 "(6, 4)";

  ]

let input = [
    t "input1" "let x = input() in x + 2" "123" "125"
  ]

let program_suite = "program_tests">:::program_tests;;
let type_suite = "type_tests">:::type_tests;;
let pair_suite = "pair_tests">:::pair_tests;;
let simple_suite = "pair_tests">:::simple_tests;;
let fv_suite = "free_vars_tests">:::fv_tests;;
let oom_suite = "oom_tests">:::oom;;
let gc_suite = "gc_tests">:::gc;;

let () =
  run_test_tt_main ("all_tests">:::[
    simple_suite;
    pair_suite;
    type_suite;
    fv_suite;
    program_suite;
    oom_suite;
    gc_suite;
    input_file_test_suite ()])
;;
