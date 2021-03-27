open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open TypeCheck

module StringSet = Set.Make(String);;
module StringMap = Map.Make(String);;
type 'a envt = 'a StringMap.t;;

let print_env env how =
  debug_printf "Env is\n";
  StringMap.iter (fun id bind -> debug_printf "  %s -> %s\n" id (how bind)) env;;


let const_true       = HexConst(0xFFFFFFFFFFFFFFFFL)
let const_false      = HexConst(0x7FFFFFFFFFFFFFFFL)
let bool_mask        = HexConst(0x8000000000000000L)
let bool_tag         = 0x0000000000000007L
let bool_tag_mask    = 0x0000000000000007L
let num_tag          = 0x0000000000000000L
let num_tag_mask     = 0x0000000000000001L
let closure_tag      = 0x0000000000000005L
let closure_tag_mask = 0x0000000000000007L
let tuple_tag        = 0x0000000000000001L
let tuple_tag_mask   = 0x0000000000000007L
let const_nil        = HexConst(tuple_tag)

let err_COMP_NOT_NUM     = 1L
let err_ARITH_NOT_NUM    = 2L
let err_LOGIC_NOT_BOOL   = 3L
let err_IF_NOT_BOOL      = 4L
let err_OVERFLOW         = 5L
let err_GET_NOT_TUPLE    = 6L
let err_GET_LOW_INDEX    = 7L
let err_GET_HIGH_INDEX   = 8L
let err_NIL_DEREF        = 9L
let err_OUT_OF_MEMORY    = 10L
let err_SET_NOT_TUPLE    = 11L
let err_SET_LOW_INDEX    = 12L
let err_SET_HIGH_INDEX   = 13L
let err_CALL_NOT_CLOSURE = 14L
let err_CALL_ARITY_ERR   = 15L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]
let heap_reg = R15
let scratch_reg = R11

                             
(* Prepends a list-like env onto an envt *)
let merge_envs list_env1 env2 =
  List.fold_right (fun (id, offset) env -> StringMap.add id offset env) list_env1 env2
;;
(* Combines two envts into one, preferring the first one *)
let prepend env1 env2 = StringMap.union (fun _ a _ -> Some a) env1 env2
;;
let env_keys e = List.map fst (StringMap.bindings e);;

(* Scope_info stores the location where something was defined,
   and if it was a function declaration, then its type arity and argument arity *)
type scope_info = (sourcespan * int option * int option)
let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E e (env : scope_info envt) (tyenv : StringSet.t) =
    debug_printf "In wf_E: %s\n" (ExtString.String.join ", " (env_keys env));
    match e with
    | ESeq(e1, e2, _) -> wf_E e1 env tyenv @ wf_E e2 env tyenv
    | ETuple(es, _) -> List.concat (List.map (fun e -> wf_E e env tyenv) es)
    | EGetItem(e, idx, len, pos) ->
       (if idx >= len || len < 0 || idx < 0 then [Arity(len, idx, pos)] else [])
       @ wf_E e env tyenv
    | ESetItem(e, idx, len, newval, pos) ->
       (if idx >= len || len < 0 || idx < 0 then [Arity(len, idx, pos)] else [])
       @ wf_E e env tyenv @ wf_E newval env tyenv
    | EAnnot(e, t, _) -> wf_E e env tyenv @ wf_T tyenv t
    | ENil _ -> []
    | EBool _ -> []
    | ENumber(n, loc) ->
       if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L) then
         [Overflow(n, loc)]
       else
         []
    | EId (x, loc) -> if StringMap.mem x env then [] else [UnboundId(x, loc)]
    | EPrim1(_, _, e, _) -> wf_E e env tyenv
    | EPrim2(_, _, l, r, _) -> wf_E l env tyenv @ wf_E r env tyenv
    | EIf(c, t, f, _) -> wf_E c env tyenv @ wf_E t env tyenv @ wf_E f env tyenv
    | ELet(bindings, body, _) ->
       let rec find_locs x (binds : 'a bind list) : 'a list =
         match binds with
         | [] -> []
         | BBlank _::rest -> find_locs x rest
         | BName(y, _, _, loc)::rest ->
            if x = y then loc :: find_locs x rest
            else  find_locs x rest
         | BTuple(binds, _)::rest -> find_locs x binds @ find_locs x rest in
       let rec find_dupes (binds : 'a bind list) : exn list =
         match binds with
         | [] -> []
         | (BBlank _::rest) -> find_dupes rest
         | (BName(x, _, _, def)::rest) -> (List.map (fun use -> DuplicateId(x, use, def)) (find_locs x rest)) @ (find_dupes rest)
         | (BTuple(binds, _)::rest) -> find_dupes (binds @ rest) in
       let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) bindings) in
       let rec process_binds (rem_binds : 'a bind list) (env : scope_info envt) =
         match rem_binds with
         | [] -> (env, [])
         | BBlank _::rest -> process_binds rest env
         | BTuple(binds, _)::rest -> process_binds (binds @ rest) env
         | BName(x, allow_shadow, typ, xloc)::rest ->
            let shadow =
              if allow_shadow then []
              else match StringMap.find_opt x env with
                   | None -> []
                   | Some (existing, _, _) -> [ShadowId(x, xloc, existing)] in
            let new_env = StringMap.add x (xloc, None, None) env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs)) in
       let rec process_bindings bindings (env : scope_info envt) =
         match bindings with
         | [] -> (env, [])
         | (b, e, loc)::rest ->
            let errs_e = wf_E e env tyenv in
            let (env', errs) = process_binds [b] env in
            let (env'', errs') = process_bindings rest env' in
            (env'', errs @ errs_e @ errs') in
       let (env2, errs) = process_bindings bindings env in
       dupeIds @ errs @ wf_E body env2 tyenv
    | EApp(func, None, args, native, loc) ->
       let rec_errors = List.concat (List.map (fun e -> wf_E e env tyenv) (func :: args)) in
       (match func with
        | EId(funname, _) -> 
           (match (StringMap.find_opt funname env) with
            | Some(_, _, Some arg_arity) ->
               let actual = List.length args in
               if actual != arg_arity then [Arity(arg_arity, actual, loc)] else []
            | _ -> [])
        | _ -> [])
       @ rec_errors
    | EApp(func, Some typs, args, native, loc) ->
       let rec_errors = List.concat (List.map (fun e -> wf_E e env tyenv) (func :: args)) in
       (match func with
        | EId(funname, _) -> 
           (match (StringMap.find_opt funname env) with
            | Some(_, Some typ_arity, Some arg_arity) ->
               let actual_args = List.length args in
               if actual_args != arg_arity
               then [Arity(arg_arity, actual_args, loc)]
               else let actual_typs = List.length typs in
                    if actual_typs != typ_arity
                    then [Arity(typ_arity, actual_typs, loc)]
                    else []
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
         | BName(y, _, _, loc)::rest ->
            if x = y then loc :: find_locs x rest
            else  find_locs x rest
         | BTuple(binds, _)::rest -> find_locs x binds @ find_locs x rest in
       let rec find_dupes (binds : 'a bind list) : exn list =
         match binds with
         | [] -> []
         | (BBlank _::rest) -> find_dupes rest
         | (BName(x, _, _, def)::rest) -> List.map (fun use -> DuplicateId(x, use, def)) (find_locs x rest)
         | (BTuple(binds, _)::rest) -> find_dupes (binds @ rest) in
       let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) binds) in
       let rec process_binds (rem_binds : sourcespan bind list) (env : scope_info envt) =
         match rem_binds with
         | [] -> (env, [])
         | BBlank _::rest -> process_binds rest env
         | BTuple(binds, _)::rest -> process_binds (binds @ rest) env
         | BName(x, allow_shadow, typ, xloc)::rest ->
            let shadow =
              if allow_shadow then []
              else match StringMap.find_opt x env with
                   | None -> []
                   | Some (existing, _, _) -> if xloc = existing then [] else [ShadowId(x, xloc, existing)] in
            let new_env = StringMap.add x (xloc, None, None) env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs)) in

       let (env, bind_errs) = process_binds (List.map (fun (b, _, _) -> b) binds) env in
       
       let rec process_bindings bindings env =
         match bindings with
         | [] -> (env, [])
         | (b, e, loc)::rest ->
            let (env, errs) = process_binds [b] env in
            let errs_e = wf_E e env tyenv in
            let (env', errs') = process_bindings rest env in
            (env', errs @ errs_e @ errs') in
       let (new_env, binding_errs) = process_bindings binds env in

       let rhs_problems = List.map (fun (_, rhs, _) -> wf_E rhs new_env tyenv) binds in
       let body_problems = wf_E body new_env tyenv in
       nonfun_errs @ dupeIds @ bind_errs @ binding_errs @ (List.flatten rhs_problems) @ body_problems
    | ELambda(binds, body, _) ->
       let rec dupe x args =
         match args with
         | [] -> None
         | BName(y, _, _, loc)::_ when x = y -> Some loc
         | BTuple(binds, _)::rest -> dupe x (binds @ rest)
         | _::rest -> dupe x rest in
       let rec process_args rem_args =
         match rem_args with
         | [] -> []
         | BBlank _::rest -> process_args rest
         | BName(x, _, _, loc)::rest ->
            (match dupe x rest with
             | None -> []
             | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest
         | BTuple(binds, loc)::rest ->
            process_args (binds @ rest)
       in
       let rec flatten_bind (bind : sourcespan bind) : (string * scope_info) list =
         match bind with
         | BBlank _ -> []
         | BName(x, _, _, xloc) -> [(x, (xloc, None, None))]
         | BTuple(args, _) -> List.concat (List.map flatten_bind args) in
       (process_args binds) @ wf_E body (merge_envs (List.concat (List.map flatten_bind binds)) env) tyenv
  and wf_D d (env : scope_info envt) (tyenv : StringSet.t) =
    match d with
    | DFun(_, args, typ, body, _) ->
       let rec dupe x args =
         match args with
         | [] -> None
         | BName(y, _, _, loc)::_ when x = y -> Some loc
         | BTuple(binds, _)::rest -> dupe x (binds @ rest)
         | _::rest -> dupe x rest in
       let rec process_args rem_args =
         match rem_args with
         | [] -> []
         | BBlank _::rest -> process_args rest
         | BName(x, _, _, loc)::rest ->
            (match dupe x rest with
             | None -> []
             | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest
         | BTuple(binds, loc)::rest ->
            process_args (binds @ rest)
       in
       let rec arg_env args (env : scope_info envt) =
         match args with
         | [] -> env
         | BBlank _ :: rest -> arg_env rest env
         | BName(name, _, _, loc)::rest -> StringMap.add name (loc, None, None) (arg_env rest env)
         | BTuple(binds, _)::rest -> arg_env (binds @ rest) env in
       (wf_S tyenv typ) @ (process_args args) @ (wf_E body (arg_env args env) tyenv)
  and wf_G (g : sourcespan decl list) (env : scope_info envt) (tyenv : StringSet.t) =
    let add_funbind (env : scope_info envt) d =
      match d with
      | DFun(name, args, SForall(tyargs, _, _), _, loc) ->
         StringMap.add name (loc, Some (List.length tyargs), Some (List.length args)) env in
    let env = List.fold_left add_funbind env g in
    let errs = List.concat (List.map (fun d -> wf_D d env tyenv) g) in
    (errs, env)
  and wf_T (tyenv : StringSet.t) (t : sourcespan typ) =
    match t with
    | TyBlank _ -> []
    | TyCon(name, loc) -> if StringSet.mem name tyenv then [] else [UnboundTyId(name, loc)]
    | TyArr(args, ret, _) -> List.flatten (List.map (wf_T tyenv) (ret :: args))
    | TyApp(scheme, args, loc) ->
       (if (StringSet.mem scheme tyenv) then [] else [UnboundTyId(scheme, loc)])
       @ List.flatten (List.map (wf_T tyenv) args)
    | TyVar(name, loc) -> if StringSet.mem name tyenv then [] else [UnboundTyId(name, loc)]
    | TyTup(args, _) -> List.flatten (List.map (wf_T tyenv) args)
  and wf_S (tyenv : StringSet.t) (s : sourcespan scheme) =
    match s with
    | SForall(args, typ, _) ->
       wf_T (StringSet.union tyenv (StringSet.of_list args)) typ
  and wf_TD (t : sourcespan tydecl) (tyenv : StringSet.t) =
    match t with
    | TyDecl(name, tyargs, args, _) ->
       let tyenv =
         match tyargs with
         | None -> StringSet.add name tyenv
         | Some tyargs -> StringSet.union (StringSet.add name tyenv) (StringSet.of_list tyargs) in
       let errs = List.flatten (List.map (wf_T tyenv) args) in
       (errs, tyenv)
  in
  match p with
  | Program(tydecls, decls, body, _) ->
     let initial_env = StringMap.mapi (fun name typ -> (get_tag_T typ, None, None)) TypeCheck.initial_val_env in
     let initial_env = StringMap.fold
                            (fun name (scheme, call_type) env ->
                              match scheme with
                              | SForall(tyargs, TyArr(args, _, _), pos) ->
                                 StringMap.add name (pos, Some (List.length tyargs), Some(List.length args)) env
                              | _ -> raise (InternalCompilerError("Found non SForall(TyArr) for function " ^ name)))
                            TypeCheck.initial_fun_env
                            initial_env in
     let rec find name (decls : 'a decl list) =
       match decls with
       | [] -> None
       | DFun(n, args, _, _, loc)::rest when n = name -> Some(loc)
       | _::rest -> find name rest in
     let rec dupe_funbinds decls =
       match decls with
       | [] -> []
       | DFun(name, args, _, _, loc)::rest ->
          (match find name rest with
          | None -> []
          | Some where -> [DuplicateFun(name, where, loc)]) @ dupe_funbinds rest in
     let all_decls = List.flatten decls in
     let helpTD (exns, tyenv) td =
       let (td_exns, tyenv) = wf_TD td tyenv in
       (exns @ td_exns, tyenv) in
     let initial_tyenv = StringSet.of_list ["Int"; "Bool"] in
     let (tydecl_errs, initial_tyenv) = List.fold_left helpTD ([], initial_tyenv) tydecls in
     let help_G (env, exns) g =
       let (g_exns, funbinds) = wf_G g env initial_tyenv in
       (StringMap.fold StringMap.add funbinds env, exns @ g_exns) in
     let (env, exns) = List.fold_left help_G (initial_env, dupe_funbinds all_decls) decls in
     debug_printf "In wf_P: %s\n" (ExtString.String.join ", " (env_keys env));
     let exns = tydecl_errs @ exns @ (wf_E body env initial_tyenv)
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
    | Program(tydecls, decls, body, tag) ->
       (* This particular desugaring will convert declgroups into ELetRecs *)
       let merge_sourcespans ((s1, _) : sourcespan) ((_, s2) : sourcespan) : sourcespan = (s1, s2) in
       let wrap_G g body =
         match g with
         | [] -> body
         | f :: r ->
            let span = List.fold_left merge_sourcespans (get_tag_D f) (List.map get_tag_D r) in
            ELetRec(helpG g, body, span) in
       Program(tydecls, [], List.fold_right wrap_G decls (helpE body), tag)
  and helpG g =
    List.map helpD g
  and helpD d =
    match d with
    | DFun(name, args, typ, body, tag) ->
       let helpArg a =
         match a with
         | BTuple(_, tag) ->
            let name = gensym "argtup" in
            let typ = bind_to_typ a in
            let newbind = BName(name, false, typ, tag) in
            (newbind, [(a, EId(name, tag), tag)])
         | _ -> (a, []) in
       let (newargs, argbinds) = List.split (List.map helpArg args) in
       let newbody = ELet(List.flatten argbinds, body, tag) in
       (BName(name, false, TyBlank(get_tag_S typ), tag), ELambda(newargs, helpE newbody, tag), tag)
  and helpBE bind =
    let (b, e, btag) = bind in
    let e = helpE e in
    match b with
    | BTuple(binds, ttag) ->
       let typ = bind_to_typ b in
       (match e with
        | EId _ ->
           expandTuple binds ttag typ e
        | _ ->
           let newname = gensym "tup" in
           (BName(newname, false, typ, ttag), e, btag) :: expandTuple binds ttag typ (EId(newname, ttag)))
    | _ -> [(b, e, btag)]
  and expandTuple binds tag typ source : sourcespan binding list =
    let len = List.length binds in
    let helpB i b =
      match b with
      | BBlank _ -> []
      | BName(name, _, typ, btag) -> [(b, EGetItem(source, i, len, tag), btag)]
      | BTuple(binds, tag) ->
         let newname = gensym "tup" in
         let newexpr = EId(newname, tag) in
         let t = match typ with
           | TyTup(typs, _) -> (List.nth typs i)
           | _ -> TyBlank tag in
         (BName(newname, false, t, tag), EGetItem(source, i, len, tag), tag) :: expandTuple binds tag t newexpr in
    List.flatten (List.mapi helpB binds)
  and helpE e =
    match e with
    | ESeq(e1, e2, tag) -> ELet([(BBlank(TyBlank tag, tag), helpE e1, tag)], helpE e2, tag)
    | ETuple(exprs, tag) -> ETuple(List.map helpE exprs, tag)
    | EGetItem(e, idx, len, tag) -> EGetItem(helpE e, idx, len, tag)
    | ESetItem(e, idx, len, newval, tag) -> ESetItem(helpE e, idx, len, helpE newval, tag)
    | EId(x, tag) -> EId(x, tag)
    | ENumber(n, tag) -> ENumber(n, tag)
    | EBool(b, tag) -> EBool(b, tag)
    | ENil(t, tag) -> ENil(t, tag)
    | EAnnot(e, t, tag) -> EAnnot(helpE e, t, tag)
    | EPrim1(op, opt_typs, e, tag) ->
       EPrim1(op, opt_typs, helpE e, tag)
    | EPrim2(op, opt_typs, e1, e2, tag) ->
       EPrim2(op, opt_typs, helpE e1, helpE e2, tag)
    | ELet(binds, body, tag) ->
       let newbinds = (List.map helpBE binds) in
       List.fold_right (fun binds body -> ELet(binds, body, tag)) newbinds (helpE body)
    | ELetRec(bindexps, body, tag) ->
       (* ASSUMES well-formed letrec, so only BName bindings *)
       let newbinds = (List.map (fun (bind, e, tag) -> (bind, helpE e, tag)) bindexps) in
       ELetRec(newbinds, helpE body, tag)
    | EIf(cond, thn, els, tag) ->
       EIf(helpE cond, helpE thn, helpE els, tag)
    | EApp(name, typs, args, native, tag) ->
       EApp(helpE name, typs, List.map helpE args, native, tag)
    | ELambda(binds, body, tag) ->
       let expandBind bind =
         match bind with
         | BTuple(_, btag) ->
            let typ = bind_to_typ bind in
            let newparam = gensym "tuparg" in
            (BName(newparam, false, typ, btag), helpBE (bind, EId(newparam, btag), btag))
         | _ -> (bind, []) in
       let (params, newbinds) = List.split (List.map expandBind binds) in
       let newbody = List.fold_right (fun binds body -> ELet(binds, body, tag)) newbinds (helpE body) in
       ELambda(params, newbody, tag)

  in helpP p
;;

(* ASSUMES desugaring is complete *)
let rename_and_tag (p : tag program) : tag program =
  let rec rename (env : (string * call_type option) envt) p =
    match p with
    | Program(tydecls, [], body, tag) ->
       let initial_funenv = StringMap.mapi (fun name (_, ct) -> (name, Some ct)) TypeCheck.initial_fun_env in
       let initial_env = prepend env initial_funenv in
       Program(tydecls, [], helpE initial_env body, tag)
    | Program(_, _, _, _) -> raise (InternalCompilerError "Renaming program should have been desugared already")
  and helpB (env : (string * call_type option) envt) b =
    match b with
    | BBlank(typ, tag) -> (b, env)
    | BName(name, allow_shadow, typ, tag) ->
       let name' = sprintf "%s_%d" name tag in
       (BName(name', allow_shadow, typ, tag), StringMap.add name (name', None) env)
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
    | EAnnot(e, t, tag) -> helpE env e
    | ESeq(e1, e2, tag) -> ESeq(helpE env e1, helpE env e2, tag)
    | ETuple(es, tag) -> ETuple(List.map (helpE env) es, tag)
    | EGetItem(e, idx, len, tag) -> EGetItem(helpE env e, idx, len, tag)
    | ESetItem(e, idx, len, newval, tag) -> ESetItem(helpE env e, idx, len, helpE env newval, tag)
    | EPrim1(op, opt_typs, arg, tag) -> EPrim1(op, opt_typs, helpE env arg, tag)
    | EPrim2(op, opt_typs, left, right, tag) -> EPrim2(op, opt_typs, helpE env left, helpE env right, tag)
    | EIf(c, t, f, tag) -> EIf(helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId(name, tag) ->
       (try
         EId(fst (StringMap.find name env), tag)
        with Not_found ->
          raise (InternalCompilerError(sprintf "Could not find %s in env: <%s>" name (ExtString.String.join ", " (env_keys env)))))
    (* As a special case, if you see an EApp to a Native function by name, don't rename it --
       that name comes from assembly and should not be modified! *)
    | EApp(EId _ as func, None, args, Native, tag) ->
       EApp(func, None, List.map (helpE env) args, Native, tag)
    | EApp(func, None, args, native, tag) ->
       let func = helpE env func in
       let call_type =
         match func with
         | EId(name, _) ->
            (match StringMap.find_opt name env with None -> Snake | Some (_, Some ct) -> ct | Some _ -> Snake)
         | _ -> Snake in
       EApp(func, None, List.map (helpE env) args, call_type, tag)
    | EApp(func, Some tyargs, args, native, tag) ->
       let func = helpE env func in
       let call_type =
         match func with
         | EId(name, _) ->
            (match StringMap.find_opt name env with None -> Snake | Some (_, Some ct) -> ct | Some _ -> Snake)
         | _ -> Snake in
       EApp(func, Some tyargs, List.map (helpE env) args, call_type, tag)
    | ELet(binds, body, tag) ->
       let (binds', env') = helpBG env binds in
       let body' = helpE env' body in
       ELet(binds', body', tag)
    | ELambda(args, body, tag) ->
       let (newargs, env') = helpBS env args in
       ELambda(newargs, helpE env' body, tag)
    | ELetRec(bindexps, body, tag) ->
       let env' = List.fold_left (fun env (b, _, _) -> snd (helpB env b)) env bindexps in
       let (binds', env') = helpBG env' bindexps in
       ELetRec(binds', helpE env' body, tag)
  in (rename StringMap.empty p)
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
    | Program(_, decls, body, _) -> AProgram(List.concat(List.map helpG decls), helpA body, ())
  and helpG (g : tag decl list) : unit adecl list =
    List.map helpD g
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun(name, args, ret, body, _) ->
       let args = List.map (fun a ->
                      match a with
                      | BName(a, _, _, _) -> a
                      | _ -> raise (InternalCompilerError("Tuple bindings should have been desugared away"))) args in
       ADFun(name, args, helpA body, ())
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) = 
    match e with
    | EAnnot(e, _, _) -> helpC e
    | EPrim1(op, _, arg, _) ->
       let (arg_imm, arg_setup) = helpI arg in
       (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, _, left, right, _) ->
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet([], body, _) -> helpC body
    | ELet((BBlank(_, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELet((BName(bind, _, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, _) ->
       let processBind (bind, rhs, _) =
         match bind with
         | BName(name, _, _, _) -> (name, helpC rhs)
         | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                                             (string_of_bind bind))) in
       let (names, new_binds_setup) = List.split (List.map processBind binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (body_ans, (BLetRec (List.combine names new_binds)) :: body_setup)
    | ELambda(args, body, _) ->
       let processBind bind =
         match bind with
         | BName(name, _, _, _) -> name
         | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                                             (string_of_bind bind))) in
       (CLambda(List.map processBind args, helpA body, ()), [])
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
       raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | EApp(func, _, args, native, _) ->
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
    | EGetItem(tup, idx, len, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       (CGetItem(tup_imm, idx, ()), tup_setup)
    | ESetItem(tup, idx, len, newval, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (new_imm, new_setup) = helpI newval in
       (CSetItem(tup_imm, idx, new_imm, ()), tup_setup @ new_setup)
         

    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | ENil _ -> (ImmNil(), [])
    | EAnnot(e, _, _) -> helpI e

    | ESeq(e1, e2, _) ->
       let (e1_imm, e1_setup) = helpI e1 in
       let (e2_imm, e2_setup) = helpI e2 in
       (e2_imm, e1_setup @ e2_setup)


    | ETuple(args, tag) ->
       let tmp = sprintf "tup_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat new_setup) @ [BLet (tmp, CTuple(new_args, ()))])
    | EGetItem(tup, idx, len, tag) ->
       let tmp = sprintf "get_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       (ImmId(tmp, ()), tup_setup @ [BLet (tmp, CGetItem(tup_imm, idx, ()))])
    | ESetItem(tup, idx, len, newval, tag) ->
       let tmp = sprintf "set_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (new_imm, new_setup) = helpI newval in
       (ImmId(tmp, ()), tup_setup @ new_setup @ [BLet (tmp, CSetItem(tup_imm, idx, new_imm,()))])

    | EPrim1(op, _, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [BLet (tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, _, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [BLet (tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [BLet (tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, _, args, native, tag) ->
       let tmp = sprintf "app_%d" tag in
       let (new_func, func_setup) = helpI func in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), func_setup @ (List.concat new_setup) @ [BLet (tmp, CApp(new_func, new_args, native, ()))])
    | ELet([], body, _) -> helpI body
    | ELet((BBlank(_, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELetRec(binds, body, tag) ->
       let tmp = sprintf "lam_%d" tag in
       let processBind (bind, rhs, _) =
         match bind with
         | BName(name, _, _, _) -> (name, helpC rhs)
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
         | BName(name, _, _, _) -> name
         | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                                             (string_of_bind bind))) in
       (ImmId(tmp, ()), [BLet(tmp, CLambda(List.map processBind args, helpA body, ()))])
    | ELet((BName(bind, _, _, _), exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
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


let free_vars_E (e : 'a aexpr) rec_binds : string list =
  let rec helpA (bound : string list) (e : 'a aexpr) : string list =
    match e with
    | ASeq(e1, e2, _) -> helpC bound e1 @ helpA bound e2
    | ALet(name, binding, body, _) ->
     (helpC bound binding) (* all the free variables in the binding, plus *)
     (* all the free variables in the body, except the name itself *)
     @ (helpA (name :: bound) body)
    | ALetRec(bindings, body, _) ->
       let names = List.map fst bindings in
       let new_bound = (names @ bound) in
        (helpA new_bound body) @ List.flatten (List.map (fun binding -> helpC new_bound (snd binding)) bindings)
    | ACExpr c -> helpC bound c
  and helpC (bound : string list) (e : 'a cexpr) : string list =
    match e with
    | CLambda(args, body, _) ->
      helpA (args @ bound) body
    | CIf(cond, thn, els, _) ->
      helpI bound cond @ helpA bound thn @ helpA bound els
    | CPrim1(_, arg, _) -> helpI bound arg
    | CPrim2(_, left, right, _) -> helpI bound left @ helpI bound right
    (* This special case notices when you are calling a Native function by name,
       and ignores that name as a "free variable" at the level of Snake variable names *)
    | CApp(ImmId _, args, Native, _) ->
       (List.flatten (List.map (fun arg -> helpI bound arg) args))
    | CApp(fn, args, _, _) ->
      (helpI bound fn) @ (List.flatten (List.map (fun arg -> helpI bound arg) args))
    | CTuple(vals, _) -> List.flatten (List.map (fun v -> helpI bound v) vals)
    | CGetItem(tup, _, _) -> helpI bound tup
    | CSetItem(tup, _, rhs, _) -> helpI bound tup @ helpI bound rhs
    | CImmExpr i -> helpI bound i
  and helpI (bound : string list) (e : 'a immexpr) : string list =
    match e with
    | ImmId(name, _) ->
      (* a name is free if it is not bound *)
      if List.mem name bound then [] else [name]
    | _ -> []
  in List.sort_uniq String.compare (helpA rec_binds e)
;;
let free_vars_P (p : 'a aprogram) rec_binds : string list =
  match p with
  | AProgram(_, body, _) -> free_vars_E body rec_binds
;;


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

and reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [
    IInstrComment(IMov(Reg(RAX), LabelContents("?HEAP_END")),
                 sprintf "Reserving %d words" (size / word_size));
    ISub(Reg(RAX), Const(Int64.of_int size));
    ICmp(Reg(RAX), Reg(heap_reg));
    IJge(Label ok);
  ]
  @ (native_call (Label "?try_gc") [
         (Sized(QWORD_PTR, Reg(heap_reg))); (* alloc_ptr in C *)
         (Sized(QWORD_PTR, Const(Int64.of_int size))); (* bytes_needed in C *)
         (Sized(QWORD_PTR, Reg(RBP))); (* first_frame in C *)
         (Sized(QWORD_PTR, Reg(RSP))); (* stack_top in C *)
    ])
  @ [
      IInstrComment(IMov(Reg(heap_reg), Reg(RAX)), "assume gc success if returning here, so RAX holds the new heap_reg value");
      ILabel(ok);
    ]

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)
(* Additionally, you are provided an initial environment of values that you may want to
   assume should take up the first few stack slots.  See the compiliation of Programs
   below for one way to use this ability... *)
and compile_fun name args body initial_env = raise (NotYetImplemented "NYI: compile_fun")

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
  let wrap_native (name, (scheme, _)) =
    let arity = match scheme with
      | SForall(_, TyArr(args, _, _), _) -> List.length args
      | _ -> raise (InternalCompilerError (sprintf "Native function %s doesn't have SForall scheme: %s"
                                             name (string_of_scheme scheme))) in
    let argnames = List.init arity (fun i -> sprintf "%s_arg_%d" name i) in
    [DFun(name, List.map (fun name -> BName(name, false, TyBlank dummy_span, dummy_span)) argnames, scheme,
         EApp(EId(name, dummy_span), None, List.map (fun name -> EId(name, dummy_span)) argnames, Native, dummy_span),
      dummy_span)] in
  match p with
  | Program(tydecls, declss, body, tag) ->
     Program(tydecls, (List.map wrap_native TypeCheck.native_fun_bindings) @ declss, body, tag)

let compile_prog (was_typechecked : bool) anfed =
  let prelude =
    "section .text
extern error
extern input
extern print
extern print_stack
extern equal
extern try_gc
extern naive_print_heap
extern HEAP
extern HEAP_END
extern set_stack_bottom
global our_code_starts_here" in
  let suffix = sprintf "
err_comp_not_num:%s
err_arith_not_num:%s
err_logic_not_bool:%s
err_if_not_bool:%s
err_overflow:%s
err_get_not_tuple:%s
err_get_low_index:%s
err_get_high_index:%s
err_nil_deref:%s
err_out_of_memory:%s
err_set_not_tuple:%s
err_set_low_index:%s
err_set_high_index:%s
err_call_not_closure:%s
err_call_arity_err:%s
"
                       (to_asm (native_call (Label "error") [Const(err_COMP_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_ARITH_NOT_NUM); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_LOGIC_NOT_BOOL); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_IF_NOT_BOOL); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_OVERFLOW); Reg(RAX)]))
                       (to_asm (native_call (Label "error") [Const(err_GET_NOT_TUPLE); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_GET_LOW_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_GET_HIGH_INDEX)]))
                       (to_asm (native_call (Label "error") [Const(err_NIL_DEREF); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_OUT_OF_MEMORY); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_SET_NOT_TUPLE); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_SET_LOW_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_SET_HIGH_INDEX); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_CALL_NOT_CLOSURE); Reg(scratch_reg)]))
                       (to_asm (native_call (Label "error") [Const(err_CALL_ARITY_ERR); Reg(scratch_reg)]))
  in
  match anfed with
  | AProgram([], body, _) ->
  (* $heap and $size are mock parameter names, just so that compile_fun knows our_code_starts_here takes in 2 parameters *)
     let (prologue, comp_main, epilogue) = compile_fun "?our_code_starts_here_entry" ["$heap"; "$size"] body StringMap.empty in
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
  | AProgram(_, _, _) -> raise (InternalCompilerError "ANFed program should not have any decls remaining")
;;

let run_if should_run f =
  if should_run then f else no_op_phase
;;

let compile_to_string ?no_builtins:(no_builtins=false) (should_infer : bool) (should_check : bool) (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  (* |> (run_if should_infer (add_err_phase type_inferred type_synth)) *)
  |> (run_if should_check (add_err_phase type_checked type_check))
  |> (run_if (not no_builtins) (add_phase add_natives add_native_lambdas))
  |> (add_phase desugared desugar)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase result (compile_prog should_check))
;;
