open Exprs
open Errors
open Printf
open Pretty
open Phases

module StringMap = Map.Make(String);;
type 'a envt = 'a StringMap.t;;
type funenvt = (sourcespan scheme * call_type) envt;;

let from_bindings bindings =
  List.fold_left (fun acc (name, info) -> StringMap.add name info acc) StringMap.empty bindings
;;

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)
let tInt = TyCon("Int", dummy_span)
let tBool = TyCon("Bool", dummy_span)
let int2int = SForall([], TyArr([tInt], tInt, dummy_span), dummy_span)
let intint2int = SForall([], TyArr([tInt; tInt], tInt, dummy_span), dummy_span)
let bool2bool = SForall([], TyArr([tBool], tBool, dummy_span), dummy_span)
let boolbool2bool = SForall([], TyArr([tBool; tBool], tBool, dummy_span), dummy_span)
let int2bool = SForall([], TyArr([tInt], tBool, dummy_span), dummy_span)
let intint2bool = SForall([], TyArr([tInt; tInt], tBool, dummy_span), dummy_span)
let tyVarX = TyVar("X", dummy_span)
let anyany2bool = SForall(["X"], TyArr([tyVarX; tyVarX], tBool, dummy_span), dummy_span)
let any2any = SForall(["X"], TyArr([tyVarX], tyVarX, dummy_span), dummy_span)
let any2bool = SForall(["X"], TyArr([tyVarX], tBool, dummy_span), dummy_span)
(* create more type synonyms here, if you need to *)

let prim_bindings : (string * (sourcespan scheme * call_type)) list = [
  (* Add descriptions of all the primops here *)
  (* e.g. ("prim1:Add1", (int2int, Prim)) *)
]
let native_fun_bindings : (string * (sourcespan scheme * call_type)) list = [
  (* Add any functions that are defined by the runtime, here *)
  (* e.g. ("equal", (anyany2bool, Native)) *)
]
let initial_fun_env : (sourcespan scheme * call_type) envt = from_bindings (prim_bindings @ native_fun_bindings)
let initial_val_env : sourcespan typ envt = from_bindings [
  (* create an initial environment of any globally defined values here *)
]
let initial_typing_env = from_bindings [
  (* build up some initial typing environment here, perhaps by using the environments above somehow *)
]

let rec find_pos ls x pos =
  match StringMap.find_opt x ls with
  | None -> failwith (sprintf "Name %s not found at %s" x (string_of_sourcespan pos))
  | Some v -> v

let type_check (p : sourcespan program) : sourcespan program fallible =
  let rec same_typ t1 t2 =
    raise (NotYetImplemented "Implement sameness checking for types")
  in
  let rec checkP ((errs : exn list), (env : sourcespan typ envt)) (p : sourcespan program) =
    raise (NotYetImplemented "Implement type checking for programs")
  and checkG ((errs : exn list), (env : sourcespan typ envt)) (d : sourcespan decl list) =
    raise (NotYetImplemented "Implement type checking for declaration groups")
  and checkD ((errs : exn list), (env : sourcespan typ envt)) (d : sourcespan decl) =
    raise (NotYetImplemented "Implement type checking for declarations")
  and checkE ((errs : exn list), (env : sourcespan typ envt)) (e : sourcespan expr) (t : sourcespan typ) =
    raise (NotYetImplemented "Implement type checking for expressions")
  in match checkP ([], initial_typing_env) p with
     | ([], _) -> Ok p
     | (exns, _) -> Error (List.rev exns)
;;
