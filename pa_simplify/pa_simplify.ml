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

   (1) start at any StVal or any expr.

   (2) bottom-up, compute free-vars.  When we get to non-expressions,
     just throw up our hands and say we don't know what the free-vars
     are (and deal with it later).

   (2') this includes cases like M.N.(e) -- b/c free-vars of e could
     be bound in the local environment, or could be bound in module
     M.N.

   (3) when we come to an application that looks like (\x.M)N where N
     is pure, reduce to M[N / x]. (if x is "_", winning!)

   (4) when we come to a lambda \x.(M x) (and x is not free in M,
     reduce to M.

   (5) the same is true in #3 when x, N are tuples with the same
     length (and N is pure)

 *)

module FVS = struct
  type t = option (list string) ;

  value empty = fun [ Some [] -> True | _ -> False ] ;
  value union (s1 : t) s2 = match (s1, s2) with [
    (Some s1, Some s2) -> Some (Std.union s1 s2)
  | _ -> None
  ]
  ;

  value ofList l = Some l ;
  value var s = Some [s];

  value except s1 l = match s1 with [
    None -> None
  | Some l1 -> Some (Std.subtract l1 l)
  ]
  ;

  value mem id = fun [
    None -> True
  | Some l -> List.mem id l
  ]
  ;

  value intersect (s1 : t) s2 = match (s1,s2) with [
    (Some s1, Some s2) -> Some (Std.intersect s1 s2)
  | _ -> None
  ]
  ;
end
;

module Rho = struct
  type t = list (string * (MLast.expr * FVS.t)) ;
  value dom l = List.map fst l ;
  value ofList l = l ;
  value mem id l = List.mem_assoc id l ;
  value map id l = List.assoc id l ;
  value except (rho : t) (fvs : FVS.t) = match fvs with [
    None -> []
  | Some l -> Std.filter (fun (id, _) -> not (List.mem id l)) rho
  ]
  ;
  value captures rho fvs =
    List.exists (fun (_, (_, fvs')) -> not (FVS.empty (FVS.intersect fvs fvs'))) rho ;
end
;

value patt_fvs p =
  let rec prec = fun [
    <:patt< $lid:lid$ >> -> [lid]
  | <:patt< ( $list:l$ ) >> -> List.fold_left (fun acc p -> Std.union acc (prec p)) [] l
  | <:patt< { $list:lpl$ } >> ->
    List.fold_left (fun acc -> fun (_, p) -> Std.union acc (prec p)) [] lpl
  | <:patt< $p1$ $p2$ >> ->
    Std.union (prec p1) (prec p2)
  | <:patt< $longid:_$ >> -> []
  | <:patt< ( $p$ : $_$ ) >> -> prec p

  | <:patt< _ >> -> []

  | p -> Ploc.raise (loc_of_patt p)
      (Failure Fmt.(str "patt_fvs: unimplemented %a" Pp_MLast.pp_patt p))
  ] in
  prec p
;

value pure e =
  let rec prec = fun [
    <:expr< $lid:_$ >>
  | <:expr< $uid:_$ >> -> True

  | <:expr< $_$ $_$ >> -> False
  | <:expr< $e1$ . $e2$ >> -> prec e1 && prec e2
  | <:expr< (fun [ $list:_$ ]) >> -> True
  | <:expr< ( $list:l$ ) >> -> List.for_all prec l
  | <:expr< { $list:lel$ } >> -> List.for_all (fun (_, e) -> prec e) lel
  | _ -> False
  ] in
  prec e
  ;

value conservative_freevars e =
  let rec crec = fun [
    <:expr< $uid:_$ >> -> FVS.ofList []
  | <:expr< $lid:lid$ >> -> FVS.ofList [lid]
  | <:expr< $e1$ . $e2$ >> -> FVS.union (crec e1) (crec e2)
  | e -> Ploc.raise (loc_of_expr e)
      (Failure Fmt.(str "conservative_freevars: unimplemented %a" Pp_MLast.pp_expr e))
  ] in
  crec e
;

value subst (rho : Rho.t) e =
  let rec srec rho e =
    if rho = [] then e else
      match e with [
    <:expr:< $lid:lid$ >> as e ->
    if List.mem_assoc lid rho then fst (List.assoc lid rho)
    else e

  | <:expr:< $_$ . $_$ >> as z ->
    if not (FVS.empty (FVS.intersect (FVS.ofList (Rho.dom rho)) (conservative_freevars z))) then
      failwith "caught"
    else z

  | <:expr:< $e1$ $e2$ >> -> <:expr< $srec rho e1$ $srec rho e2$ >>

  | <:expr:< ( $list:l$ ) >> ->
    <:expr< ( $list:List.map (srec rho) l$ ) >>

  | <:expr:< { $list:lel$ } >> ->
    <:expr< { $list:List.map (fun (p,e) -> (p,srec rho e)) lel$ } >>

  | <:expr:< (fun [ $list:branches$ ]) >> as e ->
    let br1 (p, whene, e) =
      let fvp = FVS.ofList (patt_fvs p) in
      if Rho.captures rho fvp then
        (p, whene, e)
      else
        let stripped_rho = Rho.except rho fvp in
        (p, vala_map (Option.map (srec stripped_rho)) whene, srec stripped_rho e) in
    <:expr< (fun [ $list:List.map br1 branches$ ]) >>

  | e -> Ploc.raise (loc_of_expr e)
      (Failure Fmt.(str "subst: unimplemented %a" Pp_MLast.pp_expr e))

  ] in
  try Some (srec rho e)
  with [ Failure "caught" -> None ]
;

value beta_reduce (l : expr) (r : expr) = () ;
value eta_reduce (l : expr) (r : expr) = () ;

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

value simplify_expr arg e = simplify e ;

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
