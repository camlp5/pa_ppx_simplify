(* camlp5r *)
(* pa_simplify.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "q_MLast.cmo";
#load "pa_extfun.cmo";

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

(*
value simplify e =
  let rec simprec = fun [
    <:expr< $lid:lid$ >> as z -> (z, FVS.ofList [lid])

  | <:expr:< (fun $lid:x$ -> $_M$) $_N$ >> as z ->
    let (_M, fvM) = simprec _M in
    let (_N, fvN) = simprec _N in
    if not (pure _N) then
      (<:expr< (fun $lid:x$ -> $_M$) $_N$ >>,
       FVS.union fvN (FVS.except fvM [x]))
    else if FVS.mem x fvM then
      match subst [(x, (_N,fvN))] _M with [
        None -> 
        (<:expr< (fun $lid:x$ -> $_M$) $_N$ >>,
         FVS.union fvN (FVS.except fvM [x]))
      | Some _M' -> do {
          beta_reduce <:expr< (fun $lid:x$ -> $_M$) $_N$ >> _M' ;
          (_M', FVS.union (FVS.except fvM [x]) fvN)
        }
      ]
    else 
      (_M, fvM)

  | <:expr:< (fun ( $lid:x$ : $t$ ) -> $_M$) $_N$ >> ->
    let (_M, fvM) = simprec _M in
    let (_N, fvN) = simprec _N in
    if not (pure _N) then
      (<:expr< (fun ( $lid:x$ : $t$ ) -> $_M$) $_N$ >>,
       FVS.union fvN (FVS.except fvM [x]))
    else if FVS.mem x fvM then
      match subst [(x, (_N,fvN))] _M with [
        None -> 
        (<:expr< (fun ( $lid:x$ : $t$ ) -> $_M$) $_N$ >>,
         FVS.union fvN (FVS.except fvM [x]))
      | Some _M' -> (_M', FVS.union (FVS.except fvM [x]) fvN)
      ]
    else 
      (_M, fvM)

  | <:expr< $e$ && True >> -> simprec e
  | <:expr< True && $e$ >> -> simprec e

  | <:expr< $e$ || False >> -> simprec e
  | <:expr< False || $e$ >> -> simprec e

  | <:expr< $e$ + 0 >> -> simprec e
  | <:expr< 0 + $e$ >> -> simprec e

  | <:expr:< $e1$ $e2$ >> ->
    let (e1, fv1) = simprec e1 in
    let (e2, fv2) = simprec e2 in
    (<:expr< $e1$ $e2$ >>, FVS.union fv1 fv2)

  | <:expr:< (fun $lid:x$ -> $_M$ $lid:x'$ ) >> as z when x = x' ->
      let (_M, fvM) = simprec _M in
      if not (FVS.mem x fvM) then do {
        eta_reduce <:expr:< (fun $lid:x$ -> $_M$ $lid:x'$ ) >> _M ;
        (_M, fvM)
      }
      else
        (<:expr:< (fun $lid:x$ -> $_M$ $lid:x$ ) >>,
         FVS.except fvM [x])

  | <:expr:< (fun ( $lid:x$ : $t$ ) -> $_M$ $lid:x'$ ) >> as z when x = x' ->
      let (_M, fvM) = simprec _M in
      if not (FVS.mem x fvM) then do {
        eta_reduce <:expr:< (fun ( $lid:x$ : $t$ ) -> $_M$ $lid:x'$ ) >> _M ;
        (_M, fvM)
      }
      else
        (<:expr:< (fun ( $lid:x$ : $t$ ) -> $_M$ $lid:x$ ) >>,
         FVS.except fvM [x])

  | <:expr:< (fun [ $list:branches$ ]) >> ->
    let br1 (p, whene, e) =
      let (whene,whenefvs) = match uv whene with [
        None -> (None, FVS.ofList[])
      | Some e -> 
        let (e, fvs) = simprec e in (Some e, fvs)
      ] in
      let (e,efvs) = simprec e in
      let fvs = FVS.except (FVS.union whenefvs efvs) (patt_fvs p) in
      ((p, <:vala< whene >>, e), fvs) in
    let branches_fvs = List.map br1 branches in
    let fvs = List.fold_left (fun acc (_, fvs) -> FVS.union acc fvs) (FVS.ofList[])  branches_fvs in
    let branches = List.map fst branches_fvs in
    (<:expr:< (fun [ $list:branches$ ]) >>, fvs)

  | <:expr:< (match $e$ with [ $list:branches$ ]) >> ->
    let (e,efvs) = simprec e in
    let br1 (p, whene, e) =
      let (whene,whenefvs) = match uv whene with [
        None -> (None, FVS.ofList[])
      | Some e -> 
        let (e, fvs) = simprec e in (Some e, fvs)
      ] in
      let (e,efvs) = simprec e in
      let fvs = FVS.except (FVS.union whenefvs efvs) (patt_fvs p) in
      ((p, <:vala< whene >>, e), fvs) in
    let branches_fvs = List.map br1 branches in
    let fvs = List.fold_left (fun acc (_, fvs) -> FVS.union acc fvs) efvs  branches_fvs in
    let branches = List.map fst branches_fvs in
    (<:expr:< (match $e$ with [ $list:branches$ ]) >>, fvs)

  | <:expr:< ( $list:l$ ) >> ->
    let lfvs = List.map simprec l in
    let fvs = List.fold_left (fun acc (_, fvs) -> FVS.union acc fvs) (FVS.ofList[])  lfvs in
    (<:expr:< ( $list:List.map fst lfvs$ ) >>, fvs)

  | e -> (e, None)

  ] in
  fst (simprec e)
;
*)
value simplify_expr arg e = e ;

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
