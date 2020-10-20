(* camlp5r *)
(* pa_simplify.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open MLast ;
open Pa_ppx_base ;
open Pa_ppx_utils ;
open Pa_passthru ;
open Ppxutil ;

  (* Plan of the code:

   (1) start at any expr.

   (2) convert to a hashconsed expr

   (3) simplify

   (4) convert back

 *)

exception Fail ;

module FVS0 = struct
  type t = list string ;

  value ofList l = Std2.hash_uniq l ;
  value union l1 l2 = Std.union l1 l2 ;
  value free_in x l = List.mem x l ;
  value not_free_in x l = not (List.mem x l) ;
  value except id l = Std.except id l ;
  value exceptl ~{bound} l = Std.subtract l bound ;
end ;

module OrNot = struct
  type t 'a = [ KNOWN of 'a | UNKNOWN ] ;
  value known x = KNOWN x ;
  value unknown () = UNKNOWN ;
  value bind x f =
    match x with [
      UNKNOWN -> UNKNOWN
    | KNOWN l -> f l ] ;
  value is_known = fun [
    KNOWN _ -> True | UNKNOWN -> False ] ;
  value is_unknown = fun [
    KNOWN _ -> False | UNKNOWN -> True ] ;

  value get_known = fun [
    KNOWN l -> l | UNKNOWN -> raise Fail ];
end ;

module FVS1 = struct
  type t = OrNot.t FVS0.t ;
  value ofList l = OrNot.known (FVS0.ofList l) ;
  value unknown () = OrNot.unknown() ;
  value is_unknown fvs = OrNot.is_unknown fvs ;
  value union l1 l2 =
    OrNot.bind l1 (fun l1 -> OrNot.bind l2 (fun l2 -> OrNot.known (FVS0.union l1 l2))) ;
  value free_in x l =
    if OrNot.is_known l then
      FVS0.free_in x (OrNot.get_known l)
    else False ;
  value not_free_in x l =
    if OrNot.is_known l then
      FVS0.not_free_in x (OrNot.get_known l)
    else False ;
  value except id l =
    OrNot.bind l (fun l -> OrNot.known (FVS0.except id l)) ;
  value exceptl ~{bound} l =
    OrNot.bind l (fun l -> OrNot.known (FVS0.exceptl ~{bound} l)) ;
end ;

module FVS = struct
  type t = { free : FVS0.t ; maybe_free : FVS0.t } ;
  value ofList l = { free = FVS0.ofList l ; maybe_free = FVS0.ofList [] } ;
  value union l1 l2 = { free = FVS0.union l1.free l2.free ; maybe_free = FVS0.union l1.maybe_free l2.maybe_free } ;
  value free_in x l = FVS0.free_in x l.free ;
  value not_free_in x l =
    FVS0.not_free_in x l.free && FVS0.not_free_in x l.maybe_free ;
  value except id l =
    { (l) with free = FVS0.except id l.free } ;
  value exceptl ~{bound} l =
    { (l) with free = FVS0.exceptl ~{bound} l.free } ;

  value maybe l = { free = FVS0.ofList [] ; maybe_free = FVS0.union l.maybe_free l.free } ;
end ;

value patt_bound_vars p =
  let rec patrec = fun [
      <:hcpatt< _ >> -> []
    | <:hcpatt< $lid:x$ >> -> [x]
    | <:hcpatt< $p1$ $p2$ >> -> (patrec p1)@(patrec p2)
    | <:hcpatt< ( $list:l$ ) >> -> List.concat (List.map patrec l)
    | <:hcpatt< $longid:_$ >> -> []
    | <:hcpatt< ( $p$ : $_$ ) >> -> patrec p
    | z ->
      let z = Camlp5_migrate.FromHC.patt z in
      Ploc.raise (MLast.loc_of_patt z) (Failure Fmt.(str "patt_bound_vars:@ %a\n%!" Pp_MLast.pp_patt z))
  ] in
  let bvs = (patrec p) in
  if not (Std.distinct bvs) then raise Fail else
  bvs
;

value freevars0 =
  let memo_freevars = ref (fun _ -> assert False) in
  let fvrec e = memo_freevars.val e in
  let fvrec0 = fun [
      <:hcexpr< $lid:id$ >> -> FVS.ofList [id]

    | <:hcexpr< $longid:_$ >> -> FVS.ofList []
    | <:hcexpr< $longid:_$ . ( $e$ ) >> ->
      FVS.maybe (fvrec e)

    | <:hcexpr< $e$ . $lilongid:_$ >> -> fvrec e

    | <:hcexpr< fun [ $list:branches$ ] >> ->
      let fv_branch (p, whene, rhs) =
        let bvars = patt_bound_vars p in
        let whene_fvs = match uv whene with [ None -> FVS.ofList [] | Some e -> fvrec e ] in
        let rhs_fvs = fvrec rhs in
        FVS.exceptl ~{bound=bvars} (FVS.union whene_fvs rhs_fvs) in
      List.fold_left FVS.union (FVS.ofList[]) (List.map fv_branch branches)

    | <:hcexpr< match $e$ with [ $list:branches$ ] >> ->
      let fv_branch (p, whene, rhs) =
        let bvars = patt_bound_vars p in
        let whene_fvs = match uv whene with [ None -> FVS.ofList [] | Some e -> fvrec e ] in
        let rhs_fvs = fvrec rhs in
        FVS.exceptl ~{bound=bvars} (FVS.union whene_fvs rhs_fvs) in
      List.fold_left FVS.union (fvrec e) (List.map fv_branch branches)

    | <:hcexpr< $e1$ $e2$ >> -> FVS.union (fvrec e1) (fvrec e2)
    | <:hcexpr< ( $list:l$ ) >> -> List.fold_left FVS.union (FVS.ofList[]) (List.map fvrec l)

    | <:hcexpr< $int:_$ >> | <:hcexpr< $str:_$ >> -> FVS.ofList[]

    | z -> 
      let z = Camlp5_migrate.FromHC.expr z in
      Ploc.raise (MLast.loc_of_expr z) (Failure Fmt.(str "freevars: unhandled expression:@ %a\n%!" Pp_MLast.pp_expr z))
  ] in do {
    memo_freevars.val := Camlp5_hashcons.HC.memo_expr fvrec0 ;
    fvrec
  }
;
value freevars x = freevars0 x ;

module Rho = struct
  type t = list (string * Camlp5_hashcons.HC.expr) ;

  value captures bv rho =
    List.exists (fun (_, rhs) -> FVS.free_in bv (freevars rhs)) rho ;
  value capturing bvs rho =
    bvs |> Std.filter (fun bv -> captures bv rho) ;
end ;

module Fresh = struct
value ctr = ref 0 ;
value freshn ?{num} () =
  let num = match num with [ None -> 0 | Some s -> int_of_string s ] in do {
    if ctr.val < num then ctr.val := num else ();
    ctr.val := 1 + ctr.val ;
    string_of_int ctr.val
  }
;
value fresh x =
  match Pcre.extract ~{pat="^(.+)([0-9]+)$"} ~{pos=0} x with [
    [|_; id; num |] -> id^(freshn ~{num=num} ())
  | exception Not_found -> x^(freshn())
  ] ;
end ;

value patt_alpha_subst rho p =
  let rec patrec = fun [
      <:hcpatt:< $lid:x$ >> ->
      <:hcpatt< $lid:if List.mem_assoc x rho then List.assoc x rho else x$ >>

    | <:hcpatt:< $p1$ $p2$ >> -> <:hcpatt< $patrec p1$ $patrec p2$ >>
    | <:hcpatt:< ( $list:l$ ) >> -> <:hcpatt< ( $list:List.map patrec l$ ) >>
    | <:hcpatt:< $longid:_$ >> as z -> z
  ] in
  patrec p
;

value rec subst rho z =
  let fvz = freevars z in
  match z with [
    <:hcexpr:< $lid:id$ >> as z ->
    if List.mem_assoc id rho then List.assoc id rho else z

  | <:hcexpr:< $longid:_$ >> as z -> z

  | <:hcexpr:< $e$ . $lilongid:lili$ >> ->
    <:hcexpr:< $subst rho e$ . $lilongid:lili$ >>

  | <:hcexpr:< $e1$ $e2$ >> -> <:hcexpr< $subst rho e1$ $subst rho e2$ >>
  | <:hcexpr:< ( $list:l$ ) >> -> <:hcexpr< ( $list:List.map (subst rho) l$ ) >>
  | <:hcexpr:< fun [ $list:branches$ ] >> ->
    (* keep only entries [x -> N] where x is free in z *)
    let rho = rho |> Std.filter (fun (id, _) -> FVS.free_in id fvz) in
    let subst_branch (p, whene, rhs) =
      let bvs = patt_bound_vars p in
      (* remove entries [x -> N] where x is bound in p *)
      let rho = rho |> Std.filter (fun (id, _) -> not (List.mem id bvs)) in
      let (p, whene, rhs) = match Rho.capturing bvs rho with [
          [] -> (p, whene, rhs)
        | l -> 
          let patt_alpha_rho = List.map (fun id -> (id, Fresh.fresh id)) l in
          let p = patt_alpha_subst patt_alpha_rho  p in
          let alpha_rho = List.map (fun (id, id') -> (id, <:hcexpr< $lid:id'$ >>)) patt_alpha_rho in
          (p, Pcaml.vala_map (Option.map (subst alpha_rho)) whene, subst alpha_rho rhs)
        ] in do {
            assert (Rho.capturing (patt_bound_vars p) rho = []) ;
            (p, Pcaml.vala_map (Option.map (subst rho)) whene, subst rho rhs)
          } in
    <:hcexpr< fun [ $list:List.map subst_branch branches$ ] >>

  | <:hcexpr:< match $e$ with [ $list:branches$ ] >> ->
    (* keep only entries [x -> N] where x is free in z *)
    let rho = rho |> Std.filter (fun (id, _) -> FVS.free_in id fvz) in
    let subst_branch (p, whene, rhs) =
      let bvs = patt_bound_vars p in
      (* remove entries [x -> N] where x is bound in p *)
      let rho = rho |> Std.filter (fun (id, _) -> not (List.mem id bvs)) in
      let (p, whene, rhs) = match Rho.capturing bvs rho with [
          [] -> (p, whene, rhs)
        | l -> 
          let patt_alpha_rho = List.map (fun id -> (id, Fresh.fresh id)) l in
          let p = patt_alpha_subst patt_alpha_rho  p in
          let alpha_rho = List.map (fun (id, id') -> (id, <:hcexpr< $lid:id'$ >>)) patt_alpha_rho in
          (p, Pcaml.vala_map (Option.map (subst alpha_rho)) whene, subst alpha_rho rhs)
        ] in do {
            assert (Rho.capturing (patt_bound_vars p) rho = []) ;
            (p, Pcaml.vala_map (Option.map (subst rho)) whene, subst rho rhs)
          } in
    <:hcexpr< match $subst rho e$ with [ $list:List.map subst_branch branches$ ] >>

    | <:hcexpr< $int:_$ >> | <:hcexpr< $str:_$ >> as z -> z
  ]
;

module Expr = struct
value unapplist e =
  let rec unrec acc = fun [
    <:hcexpr< $t$ $arg$ >> -> unrec [arg::acc] t
  | t -> (t,acc)
  ] in unrec [] e
;
end ;

value rec is_value z = match Expr.unapplist z with [
    (<:hcexpr< $lid:_$ >>, []) -> True
  | (<:hcexpr< fun [ $list:_$ ] >>, []) -> True
  | (<:hcexpr< $longid:_$ >>, l) -> List.for_all is_value l
  | _ -> False
  ]
;

value eta_simple_beta0 =
  Camlp5_hashcons.HC.memo_expr (fun [
    <:hcexpr< fun $lid:id$ -> ( $_M$ $lid:id'$ ) >> when id = id' && FVS.not_free_in id (freevars _M) -> _M
  | <:hcexpr< fun ( $lid:id$ : $_$ ) -> ( $_M$ $lid:id'$ ) >> when id = id' && FVS.not_free_in id (freevars _M) -> _M
  | <:hcexpr< (fun $lid:id$ -> $_M$) $_N$ >> as z when is_value _N ->
    try subst [(id, _N)] _M with [ Fail -> z ]
  | <:hcexpr< (fun ( $lid:id$ : $_$ ) -> $_M$) $_N$ >> as z when is_value _N ->
    try subst [(id, _N)] _M with [ Fail -> z ]
  | e -> e
  ])
;
value eta_simple_beta x = eta_simple_beta0 x ;

value rec fix f t =
  match f t with [
    t' when t != t' -> fix f t'
  | t -> t
  ]
;

value headnorm f =
  let memo_hrec = ref (fun _ -> assert False) in
  let hrec x = memo_hrec.val x in
  let hrec0 = fun t ->
    match fix f t with [
      <:hcexpr:< ($_M$ $_N$) >> as z ->
      (match hrec _M with [
         _M' when _M != _M' -> hrec <:hcexpr< ($_M'$ $_N$) >>
       | _ -> z ])
    | z -> z ] in do {
    memo_hrec.val := Camlp5_hashcons.HC.memo_expr hrec0 ;
    hrec
  }
;


value norm hnf =
  let memo_nrec = ref (fun _ -> assert False) in
  let nrec x = memo_nrec.val x in
  let nrec0 = fun t ->
    match hnf t with [
      <:hcexpr:< $lid:_$ >> as z -> z
    | <:hcexpr:< $longid:_$ >> as z -> z
    | <:hcexpr:< fun [ $list:l$ ] >> ->
        let nbranch (p, wheno, rhs) =
          (p, Pcaml.vala_map (Option.map nrec) wheno, nrec rhs) in
        <:hcexpr:< fun [ $list:List.map nbranch l$ ] >>

    | <:hcexpr:< match $e$ with [ $list:l$ ] >> ->
        let nbranch (p, wheno, rhs) =
          (p, Pcaml.vala_map (Option.map nrec) wheno, nrec rhs) in
        <:hcexpr:< match $nrec e$ with [ $list:List.map nbranch l$ ] >>

    | <:hcexpr:< $e1$ $e2$ >> -> <:hcexpr:< $nrec e1$ $nrec e2$ >>
    | <:hcexpr:< ( $list:l$ ) >> -> <:hcexpr:< ( $list:List.map nrec l$ ) >>
    | z -> z
    ] in do {
    memo_nrec.val := Camlp5_hashcons.HC.memo_expr nrec0 ;
    nrec
  }
;

value headnorm_eta_simple_beta = headnorm eta_simple_beta ;
value norm_eta_simple_beta = norm headnorm_eta_simple_beta ;

value simplify_expr arg e =
 e 
|> Camlp5_migrate.ToHC.expr
|> norm_eta_simple_beta
|> Camlp5_migrate.FromHC.expr
;

value install () = 
let ef = EF.mk () in 
let ef = EF.{ (ef) with
            expr = extfun ef.expr with [
    z ->
    fun arg fallback ->
      Some (simplify_expr arg z)
  ] } in
  Pa_passthru.(install { name = "pa_simplify"; ef =  ef ; pass = Some 99 ; before = [] ; after = [] })
;

install();
