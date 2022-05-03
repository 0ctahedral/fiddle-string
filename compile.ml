open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors

module StringSet = Set.Make(String)


type 'a name_envt = (string * 'a) list
type 'a tag_envt  = (tag * 'a) list


let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env;;


let const_true       = HexConst(0xFFFFFFFFFFFFFFFFL)
let const_false      = HexConst(0x7FFFFFFFFFFFFFFFL)
let bool_mask        = HexConst(0x8000000000000000L)
let bool_tag         = 0x000000000000000FL
let bool_tag_mask    = 0x000000000000000FL
let num_tag          = 0x0000000000000000L
let num_tag_mask     = 0x0000000000000001L
let closure_tag      = 0x0000000000000005L
let closure_tag_mask = 0x000000000000000FL
let tuple_tag        = 0x0000000000000001L
let tuple_tag_mask   = 0x000000000000000FL
let string_tag       = 0x0000000000000007L
let string_tag_mask  = 0x000000000000000FL
let const_nil        = HexConst(tuple_tag)

let err_COMP_NOT_NUM     = 1L
let err_ARITH_NOT_NUM    = 2L
let err_LOGIC_NOT_BOOL   = 3L
let err_IF_NOT_BOOL      = 4L
let err_OVERFLOW         = 5L
let err_GET_NOT_TUPLE    = 6L
let err_GET_LOW_INDEX    = 7L
let err_GET_HIGH_INDEX   = 8L
let err_GET_NOT_NUM      = 9L
let err_NIL_DEREF        = 10L
let err_OUT_OF_MEMORY    = 11L
let err_SET_NOT_TUPLE    = 12L
let err_SET_LOW_INDEX    = 13L
let err_SET_NOT_NUM      = 14L
let err_SET_HIGH_INDEX   = 15L
let err_CALL_NOT_CLOSURE = 16L
let err_CALL_ARITY_ERR   = 17L
let err_LEN_NOT_STRING   = 18L
let err_INVALID_INDEX_STRING = 19L
let err_NOT_ENOUGH_ARGS = 20L
let err_TOO_MANY_ARGS = 21L


let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos);;

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]
let heap_reg = R15
let scratch_reg = R11

(* you can add any functions or data defined by the runtime here for future use *)
let initial_val_env = [];;

let prim_bindings = [];;
let native_fun_bindings = [
  ("print", (dummy_span, None, Some(1)));
  ("input", (dummy_span, None, Some(0)));
  ("equal", (dummy_span, None, Some(2)));
];;

let initial_fun_env = prim_bindings @ native_fun_bindings;;

(* You may find some of these helpers useful *)

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq(e1, e2, _) -> max (helpC e1) (helpA e2)
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ALetRec(binds, body, _) ->
       (List.length binds) + List.fold_left max (helpA body) (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))


let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
    | [] -> None
    | (DFun(fname, _, _, _) as d)::ds_rest ->
      if name = fname then Some(d) else find_decl ds_rest name

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
    | [] -> false
    | x::xs -> (elt = x) || (find_one xs elt)

let rec find_dup (l : 'a list) : 'a option =
  match l with
    | [] -> None
    | [_x] -> None
    | x::xs ->
      if find_one xs x then Some(x) else find_dup xs
;;

let rec find_opt (env : 'a name_envt) (elt: string) : 'a option =
  match env with
  | [] -> None
  | (x, v) :: rst -> if x = elt then Some(v) else find_opt rst elt
;;
                             
(* Prepends a list-like env onto an name_envt *)
let merge_envs list_env1 list_env2 =
  list_env1 @ list_env2
;;
(* Combines two name_envts into one, preferring the first one *)
let prepend env1 env2 =
  let rec help env1 env2 =
    match env1 with
    | [] -> env2
    | ((k, _) as fst)::rst ->
      let rst_prepend = help rst env2 in
      if List.mem_assoc k env2 then rst_prepend else fst::rst_prepend
  in
  help env1 env2
;;

let env_keys e = List.map fst e;;

(* Scope_info stores the location where something was defined,
   and if it was a function declaration, then its type arity and argument arity *)
type scope_info = (sourcespan * int option * int option)
let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E e (env : scope_info name_envt) =
    debug_printf "In wf_E: %s\n" (ExtString.String.join ", " (env_keys env));
    match e with
    | ESeq(e1, e2, _) -> wf_E e1 env @ wf_E e2 env
    | ETuple(es, _) -> List.concat (List.map (fun e -> wf_E e env) es)
    | EGetItem(e, idx, _pos) ->
       wf_E e env @ wf_E idx env
    | ESetItem(e, idx, newval, _pos) ->
       wf_E e env @ wf_E idx env @ wf_E newval env
    | EPrintf(fmt, args, _) -> wf_E fmt env @ List.concat (List.map (fun e -> wf_E e env) args)
    | ESubString(e, sidx, eidx, _pos) ->
       wf_E e env @ wf_E sidx env @ wf_E eidx env
    | ENil _ -> []
    | EBool _ -> []
    | ENumber(n, loc) ->
       if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L) then
         [Overflow(n, loc)]
       else
         []
    | EString _ -> []
    | EId (x, loc) -> if (find_one (List.map fst env) x) then [] else [UnboundId(x, loc)]
    | EPrim1(_, e, _) -> wf_E e env
    | EPrim2(_, l, r, _) -> wf_E l env @ wf_E r env
    | EIf(c, t, f, _) -> wf_E c env @ wf_E t env @ wf_E f env
    | ELet(bindings, body, _) ->
       let rec find_locs x (binds : 'a bind list) : 'a list =
         match binds with
         | [] -> []
         | BBlank _::rest -> find_locs x rest
         | BName(y, _, loc)::rest ->
            if x = y then loc :: find_locs x rest
            else  find_locs x rest
         | BTuple(binds, _)::rest -> find_locs x binds @ find_locs x rest in
       let rec find_dupes (binds : 'a bind list) : exn list =
         match binds with
         | [] -> []
         | (BBlank _::rest) -> find_dupes rest
         | (BName(x, _, def)::rest) -> (List.map (fun use -> DuplicateId(x, use, def)) (find_locs x rest)) @ (find_dupes rest)
         | (BTuple(binds, _)::rest) -> find_dupes (binds @ rest) in
       let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) bindings) in
       let rec process_binds (rem_binds : 'a bind list) (env : scope_info name_envt) =
         match rem_binds with
         | [] -> (env, [])
         | BBlank _::rest -> process_binds rest env
         | BTuple(binds, _)::rest -> process_binds (binds @ rest) env
         | BName(x, allow_shadow, xloc)::rest ->
            let shadow =
              if allow_shadow then []
              else match find_opt env x with
                   | None -> []
                   | Some (existing, _, _) -> [ShadowId(x, xloc, existing)] in
            let new_env = (x, (xloc, None, None))::env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs)) in
       let rec process_bindings bindings (env : scope_info name_envt) =
         match bindings with
         | [] -> (env, [])
         | (b, e, _loc)::rest ->
            let errs_e = wf_E e env in
            let (env', errs) = process_binds [b] env in
            let (env'', errs') = process_bindings rest env' in
            (env'', errs @ errs_e @ errs') in
       let (env2, errs) = process_bindings bindings env in
       dupeIds @ errs @ wf_E body env2
    | EApp(func, args, _native, loc) ->
       let rec_errors = List.concat (List.map (fun e -> wf_E e env) (func :: args)) in
       (match func with
        | EId(funname, _) -> 
           (match (find_opt env funname) with
            | Some(_, _, Some arg_arity) ->
               let actual = List.length args in
               if actual != arg_arity then [Arity(arg_arity, actual, loc)] else []
            | _ -> [])
        | _ -> [])
       @ rec_errors
    | ELetRec(binds, body, _) ->
       let nonfuns = List.find_all (fun b -> match b with | (BName _, ELambda _, _) -> false | _ -> true) binds in
       let nonfun_errs = List.map (fun (b, _, where) -> LetRecNonFunction(b, where)) nonfuns in

     
       let rec find_locs x (binds : 'a bind list) : 'a list =
         match binds with
         | [] -> []
         | BBlank _::rest -> find_locs x rest
         | BName(y, _, loc)::rest ->
            if x = y then loc :: find_locs x rest
            else  find_locs x rest
         | BTuple(binds, _)::rest -> find_locs x binds @ find_locs x rest in
       let rec find_dupes (binds : 'a bind list) : exn list =
         match binds with
         | [] -> []
         | (BBlank _::rest) -> find_dupes rest
         | (BName(x, _, def)::rest) -> List.map (fun use -> DuplicateId(x, use, def)) (find_locs x rest)
         | (BTuple(binds, _)::rest) -> find_dupes (binds @ rest) in
       let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) binds) in
       let rec process_binds (rem_binds : sourcespan bind list) (env : scope_info name_envt) =
         match rem_binds with
         | [] -> (env, [])
         | BBlank _::rest -> process_binds rest env
         | BTuple(binds, _)::rest -> process_binds (binds @ rest) env
         | BName(x, allow_shadow, xloc)::rest ->
            let shadow =
              if allow_shadow then []
              else match (find_opt env x) with
                   | None -> []
                   | Some (existing, _, _) -> if xloc = existing then [] else [ShadowId(x, xloc, existing)] in
            let new_env = (x, (xloc, None, None))::env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs)) in

       let (env, bind_errs) = process_binds (List.map (fun (b, _, _) -> b) binds) env in
       
       let rec process_bindings bindings env =
         match bindings with
         | [] -> (env, [])
         | (b, e, _loc)::rest ->
            let (env, errs) = process_binds [b] env in
            let errs_e = wf_E e env in
            let (env', errs') = process_bindings rest env in
            (env', errs @ errs_e @ errs') in
       let (new_env, binding_errs) = process_bindings binds env in

       let rhs_problems = List.map (fun (_, rhs, _) -> wf_E rhs new_env) binds in
       let body_problems = wf_E body new_env in
       nonfun_errs @ dupeIds @ bind_errs @ binding_errs @ (List.flatten rhs_problems) @ body_problems
    | ELambda(binds, body, _) ->
       let rec dupe x args =
         match args with
         | [] -> None
         | BName(y, _, loc)::_ when x = y -> Some loc
         | BTuple(binds, _)::rest -> dupe x (binds @ rest)
         | _::rest -> dupe x rest in
       let rec process_args rem_args =
         match rem_args with
         | [] -> []
         | BBlank _::rest -> process_args rest
         | BName(x, _, loc)::rest ->
            (match dupe x rest with
             | None -> []
             | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest
         | BTuple(binds, _loc)::rest ->
            process_args (binds @ rest)
       in
       let rec flatten_bind (bind : sourcespan bind) : (string * scope_info) list =
         match bind with
         | BBlank _ -> []
         | BName(x, _, xloc) -> [(x, (xloc, None, None))]
         | BTuple(args, _) -> List.concat (List.map flatten_bind args) in
       (process_args binds) @ wf_E body (merge_envs (List.concat (List.map flatten_bind binds)) env)
  and wf_D d (env : scope_info name_envt) (_tyenv : StringSet.t) =
    match d with
    | DFun(_, args, body, _) ->
       let rec dupe x args =
         match args with
         | [] -> None
         | BName(y, _, loc)::_ when x = y -> Some loc
         | BTuple(binds, _)::rest -> dupe x (binds @ rest)
         | _::rest -> dupe x rest in
       let rec process_args rem_args =
         match rem_args with
         | [] -> []
         | BBlank _::rest -> process_args rest
         | BName(x, _, loc)::rest ->
            (match dupe x rest with
             | None -> []
             | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest
         | BTuple(binds, _loc)::rest ->
            process_args (binds @ rest)
       in
       let rec arg_env args (env : scope_info name_envt) =
         match args with
         | [] -> env
         | BBlank _ :: rest -> arg_env rest env
         | BName(name, _, loc)::rest -> (name, (loc, None, None))::(arg_env rest env)
         | BTuple(binds, _)::rest -> arg_env (binds @ rest) env in
       (process_args args) @ (wf_E body (arg_env args env))
  and wf_G (g : sourcespan decl list) (env : scope_info name_envt) (tyenv : StringSet.t) =
    let add_funbind (env : scope_info name_envt) d =
      match d with
      | DFun(name, args, _, loc) ->
         (name, (loc, Some (List.length args), Some (List.length args)))::env in
    let env = List.fold_left add_funbind env g in
    let errs = List.concat (List.map (fun d -> wf_D d env tyenv) g) in
    (errs, env)
  in
  match p with
  | Program(decls, body, _) ->
     let initial_env = initial_val_env in
     let initial_env = List.fold_left
                          (fun env (name, (_, arg_count)) -> (name, (dummy_span, Some arg_count, Some arg_count))::env)
     initial_fun_env
     initial_env in
     let rec find name (decls : 'a decl list) =
       match decls with
       | [] -> None
       | DFun(n, _args, _, loc)::_rest when n = name -> Some(loc)
       | _::rest -> find name rest in
     let rec dupe_funbinds decls =
       match decls with
       | [] -> []
       | DFun(name, _args, _, loc)::rest ->
          (match find name rest with
          | None -> []
          | Some where -> [DuplicateFun(name, where, loc)]) @ dupe_funbinds rest in
     let all_decls = List.flatten decls in
     let initial_tyenv = StringSet.of_list ["Int"; "Bool"] in
     let help_G (env, exns) g =
       let (g_exns, funbinds) = wf_G g env initial_tyenv in
       (List.fold_left (fun xs x -> x::xs) env funbinds, exns @ g_exns) in
     let (env, exns) = List.fold_left help_G (initial_env, dupe_funbinds all_decls) decls in
     debug_printf "In wf_P: %s\n" (ExtString.String.join ", " (env_keys env));
     let exns = exns @ (wf_E body env)
     in match exns with
        | [] -> Ok p
        | _ -> Error exns
;;

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let rec helpP (p : sourcespan program) =
    match p with
    | Program(decls, body, tag) ->
       (* This particular desugaring will convert declgroups into ELetRecs *)
       let merge_sourcespans ((s1, _) : sourcespan) ((_, s2) : sourcespan) : sourcespan = (s1, s2) in
       let wrap_G g body =
         match g with
         | [] -> body
         | f :: r ->
            let span = List.fold_left merge_sourcespans (get_tag_D f) (List.map get_tag_D r) in
            ELetRec(helpG g, body, span) in
       Program([], List.fold_right wrap_G decls (helpE body), tag)
  and helpG g =
    List.map helpD g
  and helpD d =
    match d with
    | DFun(name, args, body, tag) ->
       let helpArg a =
         match a with
         | BTuple(_, tag) ->
            let name = gensym "argtup" in
            let newbind = BName(name, false, tag) in
            (newbind, [(a, EId(name, tag), tag)])
         | _ -> (a, []) in
       let (newargs, argbinds) = List.split (List.map helpArg args) in
       let newbody = ELet(List.flatten argbinds, body, tag) in
       (BName(name, false, tag), ELambda(newargs, helpE newbody, tag), tag)
  and helpBE bind =
    let (b, e, btag) = bind in
    let e = helpE e in
    match b with
    | BTuple(binds, ttag) ->
       (match e with
        | EId _ ->
           expandTuple binds ttag e
        | _ ->
           let newname = gensym "tup" in
           (BName(newname, false, ttag), e, btag) :: expandTuple binds ttag (EId(newname, ttag)))
    | _ -> [(b, e, btag)]
  and expandTuple binds tag source : sourcespan binding list =
    let tupleBind i b =
      match b with
      | BBlank _btag -> []
      | BName(_, _, btag) ->
        [(b, EGetItem(source, ENumber(Int64.of_int(i), dummy_span), tag), btag)]
      | BTuple(binds, tag) ->
          let newname = gensym "tup" in
          let newexpr = EId(newname, tag) in
          (BName(newname, false, tag), EGetItem(source, ENumber(Int64.of_int(i), dummy_span), tag), tag) :: expandTuple binds tag newexpr
    in
    let size_check = EPrim2(CheckSize, source, ENumber(Int64.of_int(List.length binds), dummy_span), dummy_span) in
    let size_check_bind = (BBlank(dummy_span), size_check, dummy_span) in
    size_check_bind::(List.flatten (List.mapi tupleBind binds))
  and helpE e =
    match e with
    | ESeq(e1, e2, tag) -> ELet([(BBlank(tag), helpE e1, tag)], helpE e2, tag)
    | ETuple(exprs, tag) -> ETuple(List.map helpE exprs, tag)
    | EGetItem(e, idx, tag) -> EGetItem(helpE e, helpE idx, tag)
    | ESetItem(e, idx, newval, tag) -> ESetItem(helpE e, helpE idx, helpE newval, tag)
    | EPrintf(fmt, args, tag) -> EPrintf(helpE fmt, List.map helpE args, tag)
    | ESubString(e, sidx, eidx, tag) -> ESubString(helpE e, helpE sidx, helpE eidx, tag)
    | EId(x, tag) -> EId(x, tag)
    | ENumber(n, tag) -> ENumber(n, tag)
    | EString(s, tag) -> EString(s, tag)
    | EBool(b, tag) -> EBool(b, tag)
    | ENil(t, tag) -> ENil(t, tag)
    | EPrim1(op, e, tag) ->
       EPrim1(op, helpE e, tag)
    | EPrim2(op, e1, e2, tag) ->
       EPrim2(op, helpE e1, helpE e2, tag)
    | ELet(binds, body, tag) ->
       let newbinds = (List.map helpBE binds) in
       List.fold_right (fun binds body -> ELet(binds, body, tag)) newbinds (helpE body)
    | ELetRec(bindexps, body, tag) ->
       (* ASSUMES well-formed letrec, so only BName bindings *)
       let newbinds = (List.map (fun (bind, e, tag) -> (bind, helpE e, tag)) bindexps) in
       ELetRec(newbinds, helpE body, tag)
    | EIf(cond, thn, els, tag) ->
       EIf(helpE cond, helpE thn, helpE els, tag)
    | EApp(name, args, native, tag) ->
        let new_call_type = match native with
        | Native -> Native
        | Snake -> Snake
        | _ -> Snake in
       EApp(helpE name, List.map helpE args, new_call_type, tag)
    | ELambda(binds, body, tag) ->
       let expandBind bind =
         match bind with
         | BTuple(_, btag) ->
            let newparam = gensym "tuparg" in
            (BName(newparam, false, btag), helpBE (bind, EId(newparam, btag), btag))
         | _ -> (bind, []) in
       let (params, newbinds) = List.split (List.map expandBind binds) in
       let newbody = List.fold_right (fun binds body -> ELet(binds, body, tag)) newbinds (helpE body) in
       ELambda(params, newbody, tag)

  in helpP p
;;

(* ASSUMES desugaring is complete *)
let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program(decls, body, tag) ->
       Program(List.map (fun group -> List.map (helpD env) group) decls, helpE env body, tag)
  and helpD env decl =
    match decl with
    | DFun(name, args, body, tag) ->
       let (newArgs, env') = helpBS env args in
       DFun(name, newArgs, helpE env' body, tag)
  and helpB env b =
    match b with
    | BBlank _tag -> (b, env)
    | BName(name, allow_shadow, tag) ->
       let name' = sprintf "%s_%d" name tag in
       (BName(name', allow_shadow, tag), (name, name') :: env)
    | BTuple(binds, tag) ->
       let (binds', env') = helpBS env binds in
       (BTuple(binds', tag), env')
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> ([], env)
    | b::bs ->
       let (b', env') = helpB env b in
       let (bs', env'') = helpBS env' bs in
       (b'::bs', env'')
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a)::bindings ->
       let (b', env') = helpB env b in
       let e' = helpE env e in
       let (bindings', env'') = helpBG env' bindings in
       ((b', e', a)::bindings', env'')
  and helpE env e =
    match e with
    | ESeq(e1, e2, tag) -> ESeq(helpE env e1, helpE env e2, tag)
    | ETuple(es, tag) -> ETuple(List.map (helpE env) es, tag)
    | EGetItem(e, idx, tag) -> EGetItem(helpE env e, helpE env idx, tag)
    | ESetItem(e, idx, newval, tag) -> ESetItem(helpE env e, helpE env idx, helpE env newval, tag)
    | EPrintf(fmt, args, tag) -> EPrintf(helpE env fmt, List.map (helpE env) args, tag)
    | ESubString(e, sidx, eidx, tag) -> ESubString(helpE env e, helpE env sidx, helpE env eidx, tag)
    | EPrim1(op, arg, tag) -> EPrim1(op, helpE env arg, tag)
    | EPrim2(op, left, right, tag) -> EPrim2(op, helpE env left, helpE env right, tag)
    | EIf(c, t, f, tag) -> EIf(helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EString _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId(name, tag) ->
       (try
         EId(find env name, tag)
       with InternalCompilerError _ -> e)
    | EApp(func, args, call_type, tag) ->
       let new_func =  
       (match call_type with
       | Native -> func
       | _ -> helpE env func) in
        EApp(new_func, List.map (helpE env) args, call_type, tag)

    | ELet(binds, body, tag) ->
       let (binds', env') = helpBG env binds in
       let body' = helpE env' body in
       ELet(binds', body', tag)
    | ELetRec(bindings, body, tag) ->
       let (revbinds, env) = List.fold_left (fun (revbinds, env) (b, e, t) ->
                                 let (b, env) = helpB env b in ((b, e, t)::revbinds, env)) ([], env) bindings in
       let bindings' = List.fold_left (fun bindings (b, e, tag) -> (b, helpE env e, tag)::bindings) [] revbinds in
       let body' = helpE env body in
       ELetRec(bindings', body', tag)
    | ELambda(binds, body, tag) ->
       let (binds', env') = helpBS env binds in
       let body' = helpE env' body in
       ELambda(binds', body', tag)
  in (rename [] p)
;;


(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;; ANFING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)


type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program([], body, _) -> AProgram(helpA body, ())
    | Program _ -> raise (InternalCompilerError "decls should have been desugared away")
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) = 
    match e with
    | EPrim1(op, arg, _) ->
       let (arg_imm, arg_setup) = helpI arg in
       (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet([], body, _) -> helpC body
    | ELet((BBlank _, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, _) ->
       let processBind (bind, rhs, _) =
         match bind with
         | BName(name, _, _) -> (name, helpC rhs)
         | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                                             (string_of_bind bind))) in
       let (names, new_binds_setup) = List.split (List.map processBind binds) in
       let (new_binds, _new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (body_ans, (BLetRec (List.combine names new_binds)) :: body_setup)
    | ELambda(args, body, _) ->
       let processBind bind =
         match bind with
         | BName(name, _, _) -> name
         | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                                             (string_of_bind bind))) in
       (CLambda(List.map processBind args, helpA body, ()), [])
    | ELet((BTuple(_binds, _), _exp, _)::_rest, _body, _pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | EApp(func, args, native, _) ->
       let (func_ans, func_setup) = helpI func in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CApp(func_ans, new_args, native, ()), func_setup @ List.concat new_setup)

    | ESeq(e1, e2, _) ->
       let (e1_ans, e1_setup) = helpC e1 in
       let (e2_ans, e2_setup) = helpC e2 in
       (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)

    | ETuple(args, _) ->
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CTuple(new_args, ()), List.concat new_setup)
    | EGetItem(tup, idx, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       (CGetItem(tup_imm, idx_imm, ()), tup_setup @ idx_setup)
    | ESetItem(tup, idx, newval, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       let (new_imm, new_setup) = helpI newval in
       (CSetItem(tup_imm, idx_imm, new_imm, ()), tup_setup @ idx_setup @ new_setup)
    | ESubString(str, sidx, eidx, tag) ->
       let (str_imm, str_setup) = helpI str in
       let (sidx_imm, sidx_setup) = helpI sidx in
       let (eidx_imm, eidx_setup) = helpI eidx in
       (CSubString(str_imm, sidx_imm, eidx_imm, ()), str_setup @ sidx_setup @ eidx_setup)

    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | ENil _ -> (ImmNil(), [])

    | ESeq(e1, e2, _) ->
       let (_e1_imm, e1_setup) = helpI e1 in
       let (e2_imm, e2_setup) = helpI e2 in
       (e2_imm, e1_setup @ e2_setup)

    | EString(s, tag) ->
       let tmp = sprintf "str_%d" tag in
       (ImmId(tmp, ()),  [BLet (tmp, CString(s, ()))])
    | EPrintf(fmt, args, tag) ->
       let tmp = sprintf "printf_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       let (new_fmt, fmt_setup) = helpI fmt in
       (ImmId(tmp, ()), fmt_setup @ (List.concat new_setup) @ [BLet (tmp, CPrintf(new_fmt, new_args, ()))])
    | ESubString(str, sidx, eidx, tag) ->
       let tmp = sprintf "substr_%d" tag in
       let (str_imm, str_setup) = helpI str in
       let (sidx_imm, sidx_setup) = helpI sidx in
       let (eidx_imm, eidx_setup) = helpI eidx in
       (ImmId(tmp, ()), str_setup @ sidx_setup @ eidx_setup @ [BLet(tmp, CSubString(str_imm, sidx_imm, eidx_imm, ()))])
    | ETuple(args, tag) ->
       let tmp = sprintf "tup_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat new_setup) @ [BLet (tmp, CTuple(new_args, ()))])
    | EGetItem(tup, idx, tag) ->
       let tmp = sprintf "get_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ [BLet (tmp, CGetItem(tup_imm, idx_imm, ()))])
    | ESetItem(tup, idx, newval, tag) ->
       let tmp = sprintf "set_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       let (new_imm, new_setup) = helpI newval in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ new_setup @ [BLet (tmp, CSetItem(tup_imm, idx_imm, new_imm,()))])

    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [BLet (tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [BLet (tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [BLet (tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, args, native, tag) ->
       let tmp = sprintf "app_%d" tag in
       let (new_func, func_setup) = helpI func in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), func_setup @ (List.concat new_setup) @ [BLet (tmp, CApp(new_func, new_args, native, ()))])
    | ELet([], body, _) -> helpI body
    | ELet((BBlank _, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELetRec(binds, body, tag) ->
       let tmp = sprintf "lam_%d" tag in
       let processBind (bind, rhs, _) =
         match bind with
         | BName(name, _, _) -> (name, helpC rhs)
         | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                                             (string_of_bind bind))) in
       let (names, new_binds_setup) = List.split (List.map processBind binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (ImmId(tmp, ()), (List.concat new_setup)
                        @ [BLetRec (List.combine names new_binds)]
                        @ body_setup
                        @ [BLet(tmp, body_ans)])
    | ELambda(args, body, tag) ->
       let tmp = sprintf "lam_%d" tag in
       let processBind bind =
         match bind with
         | BName(name, _, _) -> name
         | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                                             (string_of_bind bind))) in
       (ImmId(tmp, ()), [BLet(tmp, CLambda(List.map processBind args, helpA body, ()))])
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet((BTuple(_binds, _), _exp, _)::_rest, _body, _pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq(exp) -> ASeq(exp, body, ())
        | BLet(name, exp) -> ALet(name, exp, body, ())
        | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup (ACExpr ans)
  in
  helpP p
;;

let free_vars (e: 'a aexpr) : string list =
  let rec helpA (e: 'a aexpr) (env: string list) : string list =
    match e with
    | ASeq(e1, e2, _) -> (helpC e1 env) @ (helpA e2 env)
    | ALet(name, e, body, _) -> (helpC e env) @ (helpA body (name::env))
    | ALetRec(bindings, body, _) ->
        let binding_names  = List.map (fun (name, _) -> name) bindings in
        let binding_vars = List.flatten (List.map (fun (_, ex) -> helpC ex (binding_names @ env)) bindings) in
        binding_vars @ (helpA body (binding_names @ env))
    | ACExpr(cexpr) -> helpC cexpr env
  and helpC (cexpr: 'a cexpr) (env: string list) : string list =
    match cexpr with
    | CIf(cond, thn, els, _) -> (helpI cond env) @ (helpA thn env) @ (helpA els env)
    | CPrim1(_p, imm, _) -> helpI imm env
    | CPrim2(_p, imm1, imm2, _) -> (helpI imm1 env) @ (helpI imm2 env)
    | CApp(func, args, call_type, _) ->
        (match call_type with
        | Native -> []
        | _ -> let arg_free_vars = List.flatten (List.map (fun arg -> helpI arg env) args) in
                                         (helpI func env) @ arg_free_vars)
    | CImmExpr(imm) -> helpI imm env
    | CString _ -> []
    | CPrintf(fmt, args, _) -> helpI fmt env @ (List.flatten (List.map (fun arg -> helpI arg env) args))
    | CTuple(imms, _) -> List.flatten (List.map (fun imm -> helpI imm env) imms)
    | CGetItem(tup, idx, _) -> (helpI tup env) @ (helpI idx env)
    | CSetItem(tup, idx, v, _) -> (helpI tup env) @ (helpI idx env) @ (helpI v env)
    | CSubString(str, sidx, eidx, _) -> (helpI str env) @ (helpI sidx env) @ (helpI eidx env)
    | CLambda(binds, body, _) -> helpA body (binds @ env)
  and helpI (immexpr: 'a immexpr) (env: string list) : string list =
    match immexpr with
    | ImmNum(_n, _) -> []
    | ImmBool(_b, _) -> []
    | ImmId(name, _) -> if (is_bound env name) then [] else [name]
    | ImmNil(_) -> []
  and is_bound (env: string list) (name: string) : bool =
    match env with
    | [] -> false
    | first::rest -> (first = name) || (is_bound rest name)
  in
  helpA e []
;;

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)
let naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg name_envt name_envt =
  (*

letrec:
  for each (ith) bind in the letrec:
    - add name of bind in new environment with a si = si + i
    - start with si = 0 and recurse on expression to get environment
let:
  for each (ith) bind:
    - add to current environment with si = si + i


    let rec fact = (lambda(n):
                      if n == 1:
                        1
                      else:
                        n * fact(n - 1))
            in
             fact(3)


    (("fact_28" (("n_42" (arg 0))
                  ("binop_31" (var_loc 0))
                  ("binop_38" (var_loc 1))
                  ("app_37"   (var_loc 2))))
      ("our_code_starts_here"
           (("equal_4" (var_loc 0))
            ("print_14" (var_loc 1))
            ("print_22" (var_loc 2))
            ("fact_28" (var_loc 3)))))

    going down one on the list is your parent scope
    search goes down in the list, recursively checking the parent scope
   *)
  let rec helpA (expr : tag aexpr) (env: arg name_envt name_envt) (si : int) : arg name_envt name_envt =
    match expr with
      | ASeq(bind, body, _) ->
        let bind_env = (helpC bind env si) in
        let body_env = (helpA body bind_env si) in
          body_env
      | ALet(id, bind, body, _) ->
        let post_binds_env = (add_to_first_envt env (id, RegOffset(~-si * word_size, RBP))) in
        let bind_env = (helpC bind post_binds_env (si + 1)) in
        let body_env = (helpA body bind_env (si + 1)) in
          body_env
      | ACExpr(cexpr) -> helpC cexpr env si
      | ALetRec(binds, body, _) -> 
          (* adds the binds to the body environment and then creates the env for each lambda *)
          let ((body_env, new_si), binds_env) = List.fold_left_map (fun (init_env, csi) (name, exp) ->
            let pre_fun_env = (add_to_first_envt init_env (name, RegOffset(~-csi * word_size, RBP))) in
            ((pre_fun_env, csi + 1), (helpL exp pre_fun_env csi)))
          (env, si) binds in
          let binds_env = body_env @ List.flatten binds_env in
          helpA body binds_env new_si


  and helpC (cexpr : tag cexpr) (env: arg name_envt name_envt) (si : int) : arg name_envt name_envt =
    match cexpr with
      | CIf(_cond, thn, els, _) -> 
          let thn_envt = helpA thn env si in
          let els_envt = helpA els thn_envt si in
              els_envt
      | CLambda(_, _, _) -> env @ (helpL cexpr env si)
      | _ -> env
  and helpL (cexpr : tag cexpr) (_env: arg name_envt name_envt) (_si : int) : arg name_envt name_envt =
    match cexpr with
      | CLambda(args, body, ltag) -> 
          (* INVARIANT: the variable a closure is stored in must be added to its parent envt
             before we create it.
             This allows us to look for the most recent variable declaration and use that name for
             this new environment *)
          (*let env_name = get_last_var env in*)
          let env_name = sprintf "closure_%d" ltag in
          let _, args_env = List.fold_left (fun (new_si, args_env) name ->
            (new_si + 1, (name, RegOffset(new_si * word_size, RBP))::args_env)) (3, []) args in
          let fv = (free_vars (ACExpr cexpr)) in
          let new_si, fv_env = List.fold_left (fun (new_si, fv_env) x ->
            (new_si + 1, (x, RegOffset(~-new_si * word_size, RBP)) :: fv_env)
          ) (1, []) fv  in
          let new_env = helpA body [(env_name, fv_env @ args_env)] new_si in
          new_env
      | _ -> raise (InternalCompilerError "helpL should only be called on a lambda")
  (* helper to add a variable to an environment so we don't have to do destructuring up front *)
  and add_to_first_envt (env : arg name_envt name_envt) (var : (string * arg)) : arg name_envt name_envt =
    match env with
    | (name, env)::rest -> (name, var :: env) :: rest
    | [] -> raise (InternalCompilerError "cannot add to first env of empty envt")
  in
  match prog with
    | AProgram(body, _) -> 
                            (*let body_envt = helpA body si in*)
        let body_envt = helpA body [("our_code_starts_here", [])] 1 in
                            (prog, body_envt)
;;

let rec find_var (l : arg name_envt) (name : string) : 'a option =
  match l with
    | [] -> None
    | (x, loc)::rest ->
      if x == name then Some(loc) else find_var rest name
and find_env (env : arg name_envt name_envt) (name : string) : arg name_envt =
  match env with
  | [] -> raise (InternalCompilerError (sprintf "env %s not found" name))
  | (n, cenv)::rest ->
        if n = name then cenv else find_env rest name
;;

(* looks in a given envt first, then *)
let find_var_in_envt (env : arg name_envt name_envt) (var : string) (env_name : string)= 
  let rec find_var_envt (env : arg name_envt name_envt) (name : string) = 
    match env with
    | [] -> raise (InternalCompilerError (sprintf "var %s not found" name))
    | (_, cenv)::rest ->
        match find_var cenv name with
        | Some(loc) -> loc
        | None -> find_var_envt rest name in
  if env_name = "" then
    find_var_envt env var
  else
    let targ_env = find_env env env_name in
      match find_var targ_env var with
      | None -> find_var_envt env var
      | Some(loc) -> loc
;;

let check_num (a: arg) (l: string) = [
    IMov(Reg(RDI), a);
    ITest(Reg(RDI), HexConst(num_tag_mask));
    IJnz(Label(l));
    ];;

let check_arith (a: arg) = [
    IMov(Reg(RDI), a);
    ITest(Reg(RDI), HexConst(num_tag_mask));
    IJnz(Label("?err_arith_not_num"));
    ];;

let check_comp (a: arg) = [
      IMov(Reg(RDI), a);
      ITest(Reg(RDI), HexConst(num_tag_mask));
      IJnz(Label("?err_comp_not_num"));
];;

let check_logic (a: arg) = [
      IMov(Reg(RDI), a);
      ITest(Reg(RDI), HexConst(num_tag_mask));
      IJz(Label("?err_logic_not_bool"));
];;

let check_overflow = [
      IJo(Label("?err_overflow"));
];;

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))

and reserve_size_arg size_arg tag =
  (* For testing, perform gc on each allocation *)
  let ok = sprintf "$memcheck_%d" tag in
  [
    IMov(Reg(RAX), LabelContents("?HEAP_END"));
    ISub(Reg(RAX), size_arg);
    ICmp(Reg(RAX), Reg(heap_reg));
    IJge(Label ok);
  ] @
  (native_call (Label "?try_gc") [
         (Sized(QWORD_PTR, Reg(heap_reg))); (* alloc_ptr in C *)
         (Sized(QWORD_PTR, size_arg)); (* bytes_needed in C *)
         (Sized(QWORD_PTR, Reg(RBP))); (* first_frame in C *)
         (Sized(QWORD_PTR, Reg(RSP))); (* stack_top in C *)
    ])
  @ [
      IInstrComment(IMov(Reg(heap_reg), Reg(RAX)), "assume gc success if returning here, so RAX holds the new heap_reg value");
      ILabel(ok);
    ]
and reserve size tag =
  ILineComment(sprintf "Reserving %d words" (size / word_size))::
  reserve_size_arg (Const(Int64.of_int size)) tag
(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)
(* Additionally, you are provided an initial environment of values that you may want to
   assume should take up the first few stack slots.  See the compiliation of Programs
   below for one way to use this ability... *)
 and compile_fun name args body (initial_env: arg name_envt name_envt) = (
   let env = find_env initial_env name in
   let stack_size = List.length env in
   let arity = (List.length args) in
   let push_list = ref [ILineComment("pushing dummy vals")] in
   for i = 1 to (stack_size + (stack_size mod 2)) do
     push_list := !push_list @ [IMov(Reg(scratch_reg), HexConst(0xEEEEL));
                               IMov(RegOffset(~-word_size * i, RBP), Reg(scratch_reg))]
   done;
   [
   ILineComment("prologue");
   IPush(Reg(RBP));
   IMov(Reg(RBP), Reg(RSP));
   IAdd(Reg(RSP), Const(Int64.of_int (~-word_size * (stack_size + (stack_size mod 2)))));
   ] @ !push_list,
   [ ILineComment("body") ] @ (compile_aexpr body 0 initial_env arity false name),
   [
   ILineComment("pop arguments and return?");
   IMov(Reg(RSP), Reg(RBP));
   IPop(Reg(RBP));
   IRet;
   ])
and compile_aexpr (e : tag aexpr) (si : int) (env : arg name_envt name_envt) (num_args : int) (is_tail : bool) (name : string) : instruction list =
  match e with
    | ALet(bname, bind, body, _tag) -> let comp_bind =
      match bind with
      | CLambda(_, _, _) -> (compile_cexpr bind si env num_args false bname)
      | _ -> (compile_cexpr bind si env num_args false name)
   in
                                     let comp_body = (compile_aexpr body si env num_args is_tail name) in
                                     [ILineComment("let starts here");] @ comp_bind @
                                     [IMov((find_var_in_envt env bname name), Reg(RAX))] @ comp_body

          
    | ACExpr(cexpr) -> (compile_cexpr cexpr si env num_args is_tail name)
    | ASeq(bind, body, _) -> let comp_bind = (compile_cexpr bind si env num_args false name) in
                                     let comp_body = (compile_aexpr body si env num_args is_tail name) in
                                     comp_bind @ comp_body
    | ALetRec([(bname, lambda)], body, _) ->
                                            let label = match lambda with
                                                        | CLambda(_, _, tag) -> sprintf "closure_%d" tag
                                                        | _ -> raise (InternalCompilerError "Lambda not lambda") in
                                            let comp_lambda = (compile_cexpr lambda si env num_args is_tail bname) in
                                            let comp_body = (compile_aexpr body si env num_args is_tail name) in
                                            let self_si = match (find_var_in_envt env bname label) with
                                                          | RegOffset(bytes, _) -> ~-bytes / word_size
                                                          | _ -> raise (InternalCompilerError "Environment mapping other than RegOffset")
                                            in
                                            (* Pointer to closure is in RAX, need to patch this into the closure *)
                                            let patch = [ILineComment("patch value")] @ [
                                              IMov(Reg(R11), Reg(RAX));
                                              ISub(Reg(R11), Const(closure_tag));
                                              IMov(RegOffset((self_si + 2) * word_size, R11), Reg(RAX));
                                              IMov((find_var_in_envt env bname name), Reg(RAX));
                                            ] in
                                            comp_lambda @ patch @ comp_body 
    | ALetRec(_, _, _) -> raise (InternalCompilerError "Mutually recursive functions not implemented")
and compile_cexpr (e : tag cexpr) (si : int) (env : arg name_envt name_envt) (num_args : int) (is_tail : bool) (name: string): instruction list =
  match e with
    | CImmExpr(imm) -> [IMov(Reg(RAX), compile_imm imm env name)]
    | CPrim1(prim1, imm, tag) -> (let imm_arg = (compile_imm imm env name) in
      match prim1 with
        | Add1 -> (check_arith imm_arg) @ [
            IMov(Reg(RAX), imm_arg);
            IAdd(Reg(RAX), Const(2L));
        ] @ check_overflow
        | Sub1 -> (check_arith imm_arg) @ [
            IMov(Reg(RAX), imm_arg);
            ISub(Reg(RAX), Const(2L));
            IJo(Label("?err_overflow"));
        ]
        | Not -> let is_true_label = sprintf "is_true_%d" tag in
                  let done_label = sprintf "done_%d" tag in
              (check_logic imm_arg) @ [
              IMov(Reg(RAX), imm_arg);
              IXor(Reg(RAX), HexConst(0xFFFFFFFFFFFFFFFFL));
              ITest(Reg(RAX), HexConst(0xFFFFFFFFFFFFFFFFL));
              IJz(Label(is_true_label));
              IMov(Reg(RAX), const_true);
              IJmp(Label(done_label));
              ILabel(is_true_label);
              IMov(Reg(RAX), const_false);
              ILabel(done_label);
            ]
        | IsBool -> [
              IMov(Reg(RAX), imm_arg);
              IAnd(Reg(RAX), Const(bool_tag_mask));
              IMov(Reg(R11), Const(1L));
              IMov(Reg(CL), Reg(AL));
              IShl(Reg(R11), Reg(CL));
              IShl(Reg(R11), Const(Int64.sub 63L bool_tag));
              IMov(Reg(RAX), const_false);
              IOr(Reg(RAX), Reg(R11));
            ]
        | IsNum -> [
              IMov(Reg(RAX), imm_arg);
              IAnd(Reg(RAX), Const(num_tag_mask));
              IMov(Reg(R11), Const(1L));
              IMov(Reg(CL), Reg(AL));
              IShl(Reg(R11), Reg(CL));
              IShl(Reg(R11), Const(Int64.sub 63L num_tag));
              IMov(Reg(RAX), const_false);
              IOr(Reg(RAX), Reg(R11));
            ]
        | IsString -> [
              IMov(Reg(RAX), imm_arg);
              IAnd(Reg(RAX), Const(string_tag_mask));
              IMov(Reg(R11), Const(1L));
              IMov(Reg(CL), Reg(AL));
              IShl(Reg(R11), Reg(CL));
              IShl(Reg(R11), Const(Int64.sub 63L string_tag));
              IMov(Reg(RAX), const_false);
              IOr(Reg(RAX), Reg(R11));
        ]
        | Len -> 
        let e_isstring = (compile_cexpr (CPrim1(IsString, imm, tag)) si env num_args is_tail name) in
        e_isstring @
        [
          IMov(Reg(RDI), const_true);
          ICmp(Reg(RAX), Reg(RDI));
          IMov(Reg(RAX), imm_arg);
          IJne(Label("?err_len_not_string"));

          (* remove mask *)
          ISub(Reg(RAX), Const(string_tag));
          (* get the length into rax *)
          IMov(Reg(RAX), RegOffset(0, RAX));
        ]
        | IsTuple -> [
              IMov(Reg(RAX), imm_arg);
              IAnd(Reg(RAX), Const(tuple_tag_mask));
              IMov(Reg(R11), Const(1L));
              IMov(Reg(CL), Reg(AL));
              IShl(Reg(R11), Reg(CL));
              IShl(Reg(R11), Const(Int64.sub 63L tuple_tag));
              IMov(Reg(RAX), const_false);
              IOr(Reg(RAX), Reg(R11));
        ]
        | PrintStack -> raise (NotYetImplemented "Print Stack not yet implemented")
    )

    | CPrim2(prim2, e1, e2, tag) -> 
        (let comp_e1 = (compile_imm e1 env name) in
        let comp_e2 = (compile_imm e2 env name) in
        let is_true_label = sprintf "is_true_%d" tag in
        let done_label = sprintf "done_%d" tag in
          match prim2 with
          | Plus -> check_arith(comp_e1) @ check_arith(comp_e2) @ [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            IAdd(Reg(RAX), Reg(RDI));
          ] @ check_overflow
          | Concat ->
            let get_e1_len = compile_cexpr (CPrim1(Len, e1, tag)) si env num_args is_tail name in
            let get_e2_len = compile_cexpr (CPrim1(Len, e2, tag)) si env num_args is_tail name in
            (* Get total length of concat string *)
            [ILineComment(sprintf "concat_%d" tag)] @
            get_e2_len @ [
              IPush(Reg(RAX));
            ] @ get_e1_len @ [
            (* e2 len in R11 *)
            IPop(Reg(R11));
            (* Store e1 len on stack for use later *)
            IPush(Reg(RAX));
            (* Get total length of concatenated string *)
            IAdd(Reg(R11), Reg(RAX));
            (* R11 now stores new string length in characters as snakeval, which is equivalent to machine number of bytes needed *)
            IPush(Reg(R11));
            (* Add 8 bytes for length word in new string *)
            IAdd(Reg(R11), Const(8L));
            (* Pad value to nearest multiple of 16 *)
            IAdd(Reg(R11), Const(15L));
            IShr(Reg(R11), Const(4L));
            IShl(Reg(R11), Const(4L));
            IPush(Reg(R11));
            (* Reserve space for new string *)
            ] @ reserve_size_arg (Reg(R11)) tag @ [
              (* Store new R15 temporarily in R14 *)
              IPop(Reg(R14));
              IAdd(Reg(R14), Reg(R15));
              (* First word is new combined length *)
              IPop(Reg(RAX));
              IMov(RegOffset(0, R15), Reg(RAX));
              (* Load pointer to e1 into RDI *)
              IMov(Reg(RDI), comp_e1);
              ISub(Reg(RDI), HexConst(string_tag));
              (* Length of e1 in R12 *)
              IPop(Reg(R12));
              (* Use R11 as counter, starting at first character *)
              IMov(Reg(R11), Const(0L));
              ILabel(sprintf "concat1_%d" tag);
              ICmp(Reg(R12), Reg(R11));
              IJle(Label(sprintf "done1_%d" tag));
              (* Copy a character from e1 to new string *)
              IMov(Reg(AX), RegOffsetReg(RDI, R11, 1, 8));
              IMov(RegOffsetReg(R15, R11, 1, 8), Reg(AX));
              (* Increment R11 to next character, jump back to top of loop *)
              IAdd(Reg(R11), Const(2L));
              IJmp(Label(sprintf "concat1_%d" tag));
              ILabel(sprintf "done1_%d" tag);

              (* Load pointer to e2 into RDI *)
              IMov(Reg(RDI), comp_e2);
              ISub(Reg(RDI), HexConst(string_tag));
              (* Point to next character to copy *)
              IAdd(Reg(RDI), Const(8L));
              (* Total length in R12 *)
              IMov(Reg(R12), RegOffset(0, R15));
              ILabel(sprintf "concat2_%d" tag);
              (* See if we have copied total length of new string yet *)
              ICmp(Reg(R12), Reg(R11));
              IJle(Label(sprintf "done2_%d" tag));
              (* Copy character *)
              IMov(Reg(AX), RegOffset(0, RDI));
              IMov(RegOffsetReg(R15, R11, 1, 8), Reg(AX));
              (* Increment R11 and RDI to point to next character *)
              IAdd(Reg(R11), Const(2L));
              IAdd(Reg(RDI), Const(2L));
              IJmp(Label(sprintf "concat2_%d" tag));
              ILabel(sprintf "done2_%d" tag);

              (* Tag pointer to new string, move into RAX *)
              IMov(Reg(RAX), Reg(R15));
              IAdd(Reg(RAX), HexConst(string_tag));

              (* Update R15 to new value *)
              IMov(Reg(R15), Reg(R14));
            ]
          | Minus -> check_arith(comp_e1) @ check_arith(comp_e2) @ [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            ISub(Reg(RAX), Reg(RDI));
          ] @ check_overflow
          | Times -> check_arith(comp_e1) @ check_arith(comp_e2) @ [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            IMul(Reg(RAX), Reg(RDI));
            IJo(Label("?err_overflow"));
            ISar(Reg(RAX), Const(1L));
          ]
          | And -> check_logic(comp_e1) @ check_logic(comp_e2) @ [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            IAnd(Reg(RAX), Reg(RDI));
          ]
          | Or -> check_logic(comp_e1) @ check_logic(comp_e2) @ [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            IOr(Reg(RAX), Reg(RDI));
          ]
          | Greater -> check_comp(comp_e1) @ check_comp(comp_e2) @ [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            ICmp(Reg(RAX), Reg(RDI));
            IJg(Label(is_true_label));
            IMov(Reg(RAX), const_false);
            IJmp(Label(done_label));
            ILabel(is_true_label);
            IMov(Reg(RAX), const_true);
            ILabel(done_label);
          ]
          | GreaterEq -> check_comp(comp_e1) @ check_comp(comp_e2) @ [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            ICmp(Reg(RAX), Reg(RDI));
            IJge(Label(is_true_label));
            IMov(Reg(RAX), const_false);
            IJmp(Label(done_label));
            ILabel(is_true_label);
            IMov(Reg(RAX), const_true);
            ILabel(done_label);
          ]
          | Less -> check_comp(comp_e1) @ check_comp(comp_e2) @ [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            ICmp(Reg(RAX), Reg(RDI));
            IJl(Label(is_true_label));
            IMov(Reg(RAX), const_false);
            IJmp(Label(done_label));
            ILabel(is_true_label);
            IMov(Reg(RAX), const_true);
            ILabel(done_label);
          ]
          | LessEq -> check_comp(comp_e1) @ check_comp(comp_e2) @ [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            ICmp(Reg(RAX), Reg(RDI));
            IJle(Label(is_true_label));
            IMov(Reg(RAX), const_false);
            IJmp(Label(done_label));
            ILabel(is_true_label);
            IMov(Reg(RAX), const_true);
            ILabel(done_label);
          ]
          | Eq -> [
            IMov(Reg(RAX), comp_e1);
            IMov(Reg(RDI), comp_e2);
            ICmp(Reg(RAX), Reg(RDI));
            IJe(Label(is_true_label));
            IMov(Reg(RAX), const_false);
            IJmp(Label(done_label));
            ILabel(is_true_label);
            IMov(Reg(RAX), const_true);
            ILabel(done_label);
          ]
          | CheckSize -> [

            (* put tuple in rax *)
            IMov(Reg(RAX), comp_e1);
            (* put compare in r11 *)
            IMov(Reg(R11), comp_e2);

            ISar(Reg(R11), Const(1L));
          
            (* check if too high *)
            ICmp(Reg(R11), RegOffset(-1, RAX));
            IJg(Label("?err_get_high_index"));
          ]
      )

    | CIf(cond, thn, els, tag) -> 
        (let thn_label = sprintf "if_thn_%d" tag in
        let els_label = sprintf "if_els_%d" tag in
        let done_label = sprintf "if_done_%d" tag in
        let cond_imm = (compile_imm cond env name) in
        [
          IMov(Reg(RAX), cond_imm);
          (* check if boolean *)
          ITest(Reg(RAX), HexConst(num_tag_mask));
          IJz(Label("?err_if_not_bool"));
          (* compare to true *)
          ICmp(Reg(RAX), const_true);
          IJe(Label(thn_label));
        ] @
        (*els label and condition, jump to done*)
        [ ILabel(els_label); ] @
        (compile_aexpr els si env num_args is_tail name) @
        [ IJmp(Label(done_label));
          ILabel(thn_label); ] @
        (compile_aexpr thn si env num_args is_tail name) @
        [ ILabel(done_label); ])
    | CString(s, tag) -> 
        let len = String.length s in
        (* length and string fitted into words *)
        let char_size = 2 in
        let char_per_word = word_size / char_size in
        let offset = 1 + (
          let remainder = len mod char_per_word in
          if remainder = 0 then (len / char_per_word)
          else (len / char_per_word) + 1
        ) in
        let offset_padded = offset + (offset mod 2) in
        let (_, set_string) = (String.fold_left (fun (i, acc) c ->
          (i + 1, acc @ [
            IMov(Reg(AH), Char(c));
            IMov(RegOffset(i * char_size, R15), Reg(AX));
          ])
        ) (4, [IMov(Reg(AL), Char('@'))]) s) in
        [
          ILineComment("string starts here");
        ] @ (reserve (offset_padded * word_size) tag) @
        [
          (* put length of string in heap*)
          IMov(Reg(RAX), Const(Int64.of_int (len * 2)));
          IMov(RegOffset(0 * word_size, R15), Reg(RAX));
        ] @ set_string @ [
          (* put address in RAX, mask it *)
          IMov(Reg(RAX), Reg(R15));
          IAdd(Reg(RAX), HexConst(string_tag));
          IAdd(Reg(R15), Const(Int64.of_int (word_size * offset_padded)));
          (* increase the heap pointer and pad if needed *)
          ILineComment("string ends here");
        ]
    | CPrintf(fmt, args, tag) -> 
        let new_args = [Const(Int64.of_int (List.length args))] @ (List.map (fun arg -> (compile_imm arg env name)) (fmt :: args)) in 
        native_call (Label "?our_printf") new_args
    | CTuple(exps, tag) -> 
            let total_offset, set_tuple = List.fold_left_map
            (fun offset e -> (offset + 1, [IMov(Reg(RAX), (compile_imm e env name)); IMov(RegOffset(offset * word_size, R15), Reg(RAX))]))
            1 exps in
            let total_offset_padded = (total_offset + (total_offset mod 2)) in
            [
              ILineComment("tuple starts here");
            ] @ (reserve (total_offset_padded * word_size) tag) @
            [
              (* put length of tuple in heap*)
              IMov(Reg(RAX), Const(Int64.of_int ((total_offset - 1) * 2)));
              IMov(RegOffset(0 * word_size, R15), Reg(RAX))
            ] @ List.flatten set_tuple @
            [
            (* put address in RAX, mask it *)
              IMov(Reg(RAX), Reg(R15));
              IAdd(Reg(RAX), HexConst(tuple_tag));
              IAdd(Reg(R15), Const(Int64.of_int (word_size * total_offset_padded)));
            (* increase the heap pointer and pad if needed *)
              ILineComment("tuple ends here");
            ]
    | CGetItem(e, idx, tag) -> 
        let e_istuple = (compile_cexpr (CPrim1(IsTuple, e, tag)) si env num_args is_tail name) in
        let idx_isnum = (compile_cexpr (CPrim1(IsNum, idx, tag)) si env num_args is_tail name) in
        let imm_e = compile_imm e env name in
        let imm_idx = compile_imm idx env name in
        e_istuple @
        [
          IMov(Reg(RDI), const_true);
          ICmp(Reg(RAX), Reg(RDI));
          IMov(Reg(RAX), imm_e);
          IJne(Label("?err_get_not_tuple"));
        ]
        @ idx_isnum @
        [
          IMov(Reg(RDI), const_true);
          ICmp(Reg(RAX), Reg(RDI));
          IMov(Reg(RAX), imm_idx);
          IJne(Label("?err_get_not_num"));

          IMov(Reg(RAX), imm_e);
          ISub(Reg(RAX), Const(1L));
          ICmp(Reg(RAX), Const(0L));
          IJle(Label("?err_nil_deref"));
          
          (* put index into r11 *)
          IMov(Reg(R11), imm_idx);
          ICmp(Reg(R11), Const(0L));
          IJl(Label("?err_get_low_index"));

          ICmp(Reg(R11), RegOffset(0 * word_size, RAX));
          IJge(Label("?err_get_high_index"));

          ISar(Reg(R11), Const(1L));
          IAdd(Reg(R11), Const(1L));
          (* get value*)
          IMov(Reg(RAX), RegOffsetReg(RAX, R11, word_size, 0));
        ]
    | CSetItem(e, idx, newval, tag) ->
        let e_istuple = (compile_cexpr (CPrim1(IsTuple, e, tag)) si env num_args is_tail name) in
        let idx_isnum = (compile_cexpr (CPrim1(IsNum, idx, tag)) si env num_args is_tail name) in
        let imm_e = compile_imm e env name in
        let imm_idx = compile_imm idx env name in
        let imm_newval = compile_imm newval env name in
        e_istuple @
        [
          IMov(Reg(RDI), const_true);
          ICmp(Reg(RAX), Reg(RDI));
          IMov(Reg(RAX), imm_e);
          IJne(Label("?err_set_not_tuple"));
        ]
        @ idx_isnum @
        [
          IMov(Reg(RDI), const_true);
          ICmp(Reg(RAX), Reg(RDI));
          IMov(Reg(RAX), imm_idx);
          IJne(Label("?err_set_not_num"));
        
          (* deref *)
          IMov(Reg(RAX), imm_e);
          ISub(Reg(RAX), Const(1L));
          ICmp(Reg(RAX), Const(0L));
          IJle(Label("?err_nil_deref"));
          (* put index into r11 *)
          IMov(Reg(R11), imm_idx);
          ICmp(Reg(R11), Const(0L));
          IJl(Label("?err_set_low_index"));
          ICmp(Reg(R11), RegOffset(0 * word_size, RAX));
          IJge(Label("?err_set_high_index"));

          ISar(Reg(R11), Const(1L));
          IAdd(Reg(R11), Const(1L));

          IMov(Reg(RDI), imm_newval);
          IMov(RegOffsetReg(RAX, R11, word_size, 0), Reg(RDI));
          IMov(Reg(RAX), imm_newval);
    ]
    | CSubString(str, sidx, eidx, tag) ->
      let imm_str = compile_imm str env name in
      let imm_sidx = compile_imm sidx env name in
      let imm_eidx = compile_imm eidx env name in
      let get_str_len = compile_cexpr (CPrim1(Len, str, tag)) si env num_args is_tail name in
      let sidx_isnum = (compile_cexpr (CPrim1(IsNum, sidx, tag)) si env num_args is_tail name) in
      let eidx_isnum = (compile_cexpr (CPrim1(IsNum, eidx, tag)) si env num_args is_tail name) in

      get_str_len @ [
        (* move stringlen to stack *)
        IMov(Reg(R9), Reg(RAX));
      ] @ eidx_isnum @
      [
          IMov(Reg(RDI), const_true);
          ICmp(Reg(RAX), Reg(RDI));
          IMov(Reg(RAX), imm_eidx);
          (* TODO: new error? *)
          IJne(Label("?err_set_not_num"));

          IMov(Reg(R11), imm_eidx);
          ICmp(Reg(R11), Const(0L));
          IJl(Label("?err_set_low_index"));
          ICmp(Reg(R11), Reg(R9));
          IJge(Label("?err_set_high_index"));
      ] @ sidx_isnum @
      [
          IMov(Reg(RDI), const_true);
          ICmp(Reg(RAX), Reg(RDI));
          IMov(Reg(RAX), imm_sidx);
          (* TODO: new error? *)
          IJne(Label("?err_set_not_num"));

          IMov(Reg(R11), imm_sidx);
          ICmp(Reg(R11), Const(0L));
          IJl(Label("?err_set_low_index"));
          ICmp(Reg(R11), Reg(R9));
          IJge(Label("?err_set_high_index"));

          IPush(Reg(R11));
      ] @ [
        IMov(Reg(RAX), imm_eidx);
        IMov(Reg(scratch_reg), imm_sidx);
        ISub(Reg(RAX), Reg(scratch_reg));
        IJl(Label("?err_invalid_index"));
        IPush(Reg(RAX));

        (* calculate size *)

        (* Add 8 bytes for length word in new string *)
        IAdd(Reg(RAX), Const(8L));
        (* Pad value to nearest multiple of 16 *)
        IAdd(Reg(RAX), Const(15L));
        IShr(Reg(RAX), Const(4L));
        IShl(Reg(RAX), Const(4L));
        IPush(Reg(RAX));
      ] 
      @ reserve_size_arg (Reg(RAX)) tag @ [
        (*
          r14 heap_size 
          rdi diff
          r10 start_ptr
         *)
        
        IPop(Reg(R14));
        IPop(Reg(RDI));
        IPop(Reg(R10));

        IMov(Reg(RAX), imm_str);
        ISub(Reg(RAX), Const(string_tag));
        IAdd(Reg(RAX), Const(Int64.of_int word_size));
        IAdd(Reg(R10), Reg(RAX));

        (* put length in new string *)
        IMov(RegOffset(0, R15), Reg(RDI));

        (* loop while counter is less than diff *)
        (* Use R11 as counter, starting at first character *)
        IMov(Reg(R11), Const(0L));
        ILabel(sprintf "substr_%d" tag);
        ICmp(Reg(RDI), Reg(R11));
        IJle(Label(sprintf "done1_%d" tag));
        (* Copy a character from e1 to new string *)
        IMov(Reg(AX), RegOffsetReg(R10, R11, 1, 0));
        IMov(RegOffsetReg(R15, R11, 1, 8), Reg(AX));
        (* Increment R11 to next character, jump back to top of loop *)
        IAdd(Reg(R11), Const(2L));
        IJmp(Label(sprintf "substr_%d" tag));
        ILabel(sprintf "done1_%d" tag);


        IMov(Reg(RAX), Reg(R15));
        IAdd(Reg(RAX), HexConst(string_tag));

        (* Update R15 to new value *)
        IAdd(Reg(R15), Reg(R14));
      ]

    | CLambda(binds, body, tag) ->

    let label = sprintf "%s_closure_%d" name tag in
    let after_label = sprintf "%s_after_%d" name tag in
    let arity = List.length binds in
    let env_name = sprintf "closure_%d" tag in
    let exec_env = [(name, find_env env env_name)]  in
    let closed_vars = free_vars (ACExpr(e)) in
    (* 3 words for arity, code ptr, and # of vars closed over, plus a word for each var *)
    let total_offset = 3 + (List.length closed_vars) in
    let total_offset_padded = (total_offset + (total_offset mod 2)) in
    let (prologue, fnbody, epilogue) = compile_fun env_name binds body env in
    (reserve (total_offset_padded * word_size) tag) @ 
    (* put address in RAX, mask it *)
    [
      ILineComment("begin lambda");
      IJmp(Label(after_label));
      ILabel(label); 
    ] @ prologue @
    [
      (* Get pointer to closure on heap, which is first argument *)
      IMov(Reg(RAX), RegOffset(2 * word_size, RBP));
      ISub(Reg(RAX), Const(closure_tag));

      ILineComment(sprintf "get closed vars (%d)" (List.length closed_vars));
    ] @
    (* Get values out of closure and onto stack *)
    (List.flatten (List.mapi (fun i var -> [
      IMov(Reg(scratch_reg), RegOffset(word_size * (i + 3), RAX));
      IMov((find_var_in_envt exec_env var name), Reg(scratch_reg));
    ]) closed_vars))
    @ 
    [
      ILabel(sprintf "%s_body" label);
    ] @ fnbody @ epilogue
    @ 
    [
      ILabel(after_label);
    ] @ [
      (* arity *)
      IMov(Reg(RAX), Const(Int64.of_int (arity * 2)));
      IMov(RegOffset(0 * word_size, R15), Reg(RAX));
      (* code ptr *)
      IMov(Reg(RAX), Label(label));
      IMov(RegOffset(1 * word_size, R15), Reg(RAX));
      (* number of closed over vars *)
      ILineComment(sprintf "num closed vars (%d)" (List.length closed_vars));
      IMov(Reg(RAX), Const(Int64.of_int (2 * (List.length closed_vars))));
      IMov(RegOffset(2 * word_size, R15), Reg(RAX));
    ] @
    (List.flatten (List.mapi (fun i var -> [
      IMov(Reg(RAX), (find_var_in_envt env var ""));
      IMov(RegOffset(word_size * (i + 3), R15), Reg(RAX));
    ]) closed_vars))
    @
    (* pad if needed *)
    (if (total_offset mod 2) = 0 then [] else [
      IMov(Reg(scratch_reg), Sized(QWORD_PTR, HexConst(0xEEEEL)));
      IMov(RegOffset(word_size * ((List.length closed_vars) + 3), R15), Reg(scratch_reg));
    ])
    @
    [
      IMov(Reg(RAX), Reg(R15));
      IAdd(Reg(RAX), Const(closure_tag));
    (* increase the heap pointer and pad if needed *)
      IAdd(Reg(R15), Const(Int64.of_int (word_size * total_offset_padded)));
      ILineComment("end of lambda");
    ]
| CApp(lambda_id, args, call_type, _) ->
    (match call_type with
    | Native -> 
        let rec push_args (args: arg list) (regs: reg list) : instruction list * instruction list =
          match args with
          | [] -> ([], [])
          | arg::rest -> match regs with
                          | [] -> let (rest_push, rest_pop) = (push_args rest regs) in
                                  (IPush(arg)::rest_push, rest_pop @ [IPop(Reg(RDI))])
                          | reg::regs -> let (rest_push, rest_pop) = (push_args rest regs) in
                                  (IMov(Reg(reg), arg)::rest_push, rest_pop)
        in
        let (pushes, pops) = push_args (List.map (fun arg -> compile_imm arg env name) args) first_six_args_registers in
        let name = (match lambda_id with
         | ImmId(name, _) -> name
         | _ -> raise (InternalCompilerError "expected id")
         ) in
        pushes @ [ICall(Label(name))] @ pops
    | Snake ->
      let push_all = List.flatten (List.map (fun arg -> [IMov(Reg(R11), (compile_imm arg env name)); IPush(Reg(R11))]) (List.rev args)) in
      let pop_all = (List.map (fun _ -> IPop(Reg(RDI))) args) in
      (*let _, place_all = List.fold_left_map (fun i arg -> 
        (i + 1, [
                  IMov(Reg(RAX), (compile_imm arg env));
                  IMov(RegOffset(i * word_size, RBP), Reg(RAX))
                ])
      ) 2 args in*)
      [
        IMov(Reg(RAX), (compile_imm lambda_id env name));
        IMov(Reg(R11), Reg(RAX));
        IAnd(Reg(R11), HexConst(closure_tag_mask));
        ICmp(Reg(R11), HexConst(closure_tag));
        IJne(Label("?err_call_not_closure"));
      ] @
      (if (is_tail && (List.length args) <= num_args) then
      [ILineComment("tailcall methinks");] else [])(*@ List.flatten place_all @ [IJmp() ] else []) @*)
      @ push_all @  
      [
        (* push pointer as argument *)
        IPush(Reg(RAX));
        ISub(Reg(RAX), Const(closure_tag));
        IMov(Reg(R11), RegOffset(word_size * 0, RAX));
        ICmp(Reg(R11), Const(Int64.of_int (2 * (List.length args))));
        IJne(Label("?err_call_arity_err"));
        (* Untag and call code pointer, which is second word in lambda *)
        ICall(RegOffset(word_size * 1, RAX));
        IPop(Reg(RDI));
      ] @ pop_all

    | _ -> raise (InternalCompilerError (sprintf "invalid function type %s for %s" (string_of_call_type call_type) (string_of_immexpr lambda_id)))
    ) 


and compile_imm e env ename =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find_var_in_envt env x ename)
  | ImmNil(_) -> HexConst(0x01L)

and args_help args regs =
  match args, regs with
  | arg :: args, reg :: regs ->
    IMov(Sized(QWORD_PTR, Reg(reg)), arg) :: args_help args regs
  | args, [] ->
    List.rev_map (fun arg -> IPush arg) args
  | [], _ -> []
and native_call label args =
  (* We know that on entry to every function, RSP is 16-byte aligned.
     We know that every frame is a multiple of 16 bytes.
     The call instruction pushes one return pointer onto the stack.
     The first thing we do is push RBP onto the stack
     So, we add 8 bytes of padding IFF the number of spilled args is *ODD*.
  *)
  let num_stack_args = max (List.length args - 6) 0 in
  let padding_needed = (num_stack_args mod 2) <> 0 in
  let setup = (if padding_needed
               then [IInstrComment(IPush(Sized(QWORD_PTR, Const(0L))), "Padding to 16-byte alignment")]
               else []) @ args_help args first_six_args_registers in
  let teardown =
    (if num_stack_args = 0 then []
     else [ IInstrComment(IAdd(Reg(RSP), Const(Int64.of_int(word_size * num_stack_args))),
                          sprintf "Popping %d arguments" num_stack_args) ])
    @ (if padding_needed then [IInstrComment(IAdd(Reg(RSP), Const(Int64.of_int word_size)), "Unpadding one word")]
       else []) in
  setup @ [ ICall(label) ] @ teardown

                                          
(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED -- THIS CODE WILL NOT WORK AS WRITTEN *)
and call (closure : arg) args =
  let setup = List.rev_map (fun arg ->
                  match arg with
                  | Sized _ -> IPush(arg)
                  | _ -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(RSP), Const(Int64.of_int(word_size * len))), sprintf "Popping %d arguments" len) ] in
  setup @ [ ICall(closure) ] @ teardown
;;

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
let add_native_lambdas (p : sourcespan program) =
  let wrap_native name arity =
    let argnames = List.init arity (fun i -> sprintf "%s_arg_%d" name i) in
    [DFun(name, List.map (fun name -> BName(name, false, dummy_span)) argnames, EApp(EId((sprintf "?%s" name), dummy_span), List.map(fun name -> EId(name, dummy_span)) argnames, Native, dummy_span), dummy_span)]
  in
  match p with
  | Program(declss, body, tag) ->
      Program((List.fold_left (fun declss (name, (_, _, arity_opt)) -> match arity_opt with
        | Some(arity) -> (wrap_native name arity)::declss 
        | None -> raise (InternalCompilerError "Encountered undefined arity in initial runtime function definition"))
      declss native_fun_bindings), body, tag)

let compile_prog (anfed, (env : arg name_envt name_envt)) =
  let prelude =
    "section .text
extern ?error
extern ?input
extern ?print
extern ?our_printf
extern ?print_stack
extern ?equal
extern ?try_gc
extern ?naive_print_heap
extern ?HEAP
extern ?HEAP_END
extern ?set_stack_bottom
global ?our_code_starts_here" in
  let suffix = sprintf "
?err_comp_not_num:%s
?err_arith_not_num:%s
?err_logic_not_bool:%s
?err_if_not_bool:%s
?err_overflow:%s
?err_get_not_tuple:%s
?err_get_low_index:%s
?err_get_high_index:%s
?err_nil_deref:%s
?err_out_of_memory:%s
?err_set_not_tuple:%s
?err_set_low_index:%s
?err_set_high_index:%s
?err_call_not_closure:%s
?err_call_arity_err:%s
?err_get_not_num:%s
?err_set_not_num:%s
?err_len_not_string:%s
?err_invalid_index:%s
"
                       (to_asm (native_call (Label "?error") [Const(err_COMP_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_ARITH_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_LOGIC_NOT_BOOL); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_IF_NOT_BOOL); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_OVERFLOW); Reg(RAX)]))
                       (to_asm (native_call (Label "?error") [Const(err_GET_NOT_TUPLE); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_GET_LOW_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_GET_HIGH_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_NIL_DEREF); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_OUT_OF_MEMORY); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_SET_NOT_TUPLE); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_SET_LOW_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_SET_HIGH_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_CALL_NOT_CLOSURE); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_CALL_ARITY_ERR); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_GET_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_SET_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "?error") [Const(err_LEN_NOT_STRING); Reg(RAX)]))
                       (to_asm (native_call (Label "?error") [Const(err_INVALID_INDEX_STRING); Reg(RAX)]))
  in
  match anfed with
  | AProgram(body, _) ->
  (* $heap and $size are mock parameter names, just so that compile_fun knows our_code_starts_here takes in 2 parameters *)
     let (prologue, comp_main, epilogue) = compile_fun "our_code_starts_here" ["$heap"; "$size"] body env in
     let heap_start =
       [
         ILineComment("heap start");
         IInstrComment(IMov(Sized(QWORD_PTR, Reg(heap_reg)), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
         IInstrComment(IAdd(Sized(QWORD_PTR, Reg(heap_reg)), Const(15L)), "Align it to the nearest multiple of 16");
         IMov(Reg scratch_reg, HexConst(0xFFFFFFFFFFFFFFF0L));
         IInstrComment(IAnd(Sized(QWORD_PTR, Reg(heap_reg)), Reg scratch_reg), "by adding no more than 15 to it");
       ] in
     let set_stack_bottom =
       [
         ILabel("?our_code_starts_here");
         IMov(Reg R12, Reg RDI);
       ]
       @ (native_call (Label "?set_stack_bottom") [Reg(RBP)])
       @ [
           IMov(Reg RDI, Reg R12)
         ] in
     let main = (prologue @ heap_start @ comp_main @ epilogue) in
     sprintf "%s%s%s%s\n" prelude (to_asm set_stack_bottom) (to_asm main) suffix
;;

let run_if should_run f =
  if should_run then f else no_op_phase
;;

let compile_to_string ?no_builtins:(no_builtins=false) (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (run_if (not no_builtins) (add_phase add_natives add_native_lambdas))
  |> (add_phase desugared desugar)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
