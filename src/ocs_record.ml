(* Record types *)

open Ocs_types
open Ocs_error
open Ocs_env
open Ocs_sym
open Ocs_misc

let gendef b v =
  match b with
    Vglob g -> Cdefine (g, v)
  | Vloc (d, i) -> Csetl (d, i, v)
  | _ -> raise (Error "cannot change syntactic keywords")

let currentstamp = ref 0

let mk_constr (id, stamp) c n =
  let f av =
    if Array.length av <> n then
      raise (Error (Printf.sprintf "%s: bad number of args" c));
    Srecord (id, stamp, av)
  in
  {
    prim_fun = Pfn f;
    prim_name = c;
  }

let mk_pred (_, stamp) p =
  {
    prim_fun =
      Pf1 (function Srecord (_, stamp', _) when stamp = stamp' -> Strue | _ -> Sfalse);
    prim_name = p;
  }

let mk_getter (_, stamp) fget i =
  let f = function
    | Srecord (_, stamp', av) when stamp = stamp' -> av.(i)
    | _ -> raise (Error (Printf.sprintf "%s: bad arg" fget))
  in
  {
    prim_fun = Pf1 f;
    prim_name = fget;
  }

let mk_setter (_, stamp) fset i =
  let f sv1 sv2 =
    match sv1 with
    | Srecord (_, stamp', av) when stamp = stamp' -> av.(i) <- sv2; Sunspec
    | _ -> raise (Error (Printf.sprintf "%s: bad arg" fset))
  in
  {
    prim_fun = Pf2 f;
    prim_name = fset;
  }

let mkmake_record_type e args =
  match Array.to_list args with
  | Ssymbol id :: Spair {car = Ssymbol c as symc; cdr = fields} :: (Ssymbol p as pred) :: accessors ->
    let fields = List.mapi (fun i sv -> sv, i) (list_to_caml fields) in
    let stamp = id, !currentstamp in
    let getset =
      List.map (function
          | Spair {car = Ssymbol _ as fname; cdr = Spair {car = Ssymbol sget as fget; cdr = Snull}} ->
            let i = List.assoc fname fields in
            gendef (get_var e fget) (Cval (Sprim (mk_getter stamp sget i)))
          | Spair {car = Ssymbol _ as fname; cdr = Spair {car = Ssymbol sget as fget;
                                                          cdr = Spair {car = Ssymbol sset as fset; cdr = Snull}}} ->
            let i = List.assoc fname fields in
            Cseq2 (gendef (get_var e fget) (Cval (Sprim (mk_getter stamp sget i))),
                   gendef (get_var e fset) (Cval (Sprim (mk_setter stamp sset i))))
          | _ ->
            raise (Error "make-record-type: bad args")
        ) accessors
    in
    let constr = gendef (get_var e symc) (Cval (Sprim (mk_constr stamp c (List.length fields)))) in
    let pred = gendef (get_var e pred) (Cval (Sprim (mk_pred stamp p))) in
    incr currentstamp;
    Cseqn (Array.of_list (constr :: pred :: getset))
  | _ ->
    raise (Error "make-record-type: bad args")

let init e =
  bind_name e sym_make_record_type (Vsyntax mkmake_record_type)
