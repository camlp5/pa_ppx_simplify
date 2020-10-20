A PPX Rewriter for Simplifying Generated Code

### Version

This is ``pa_ppx_simplify`` (alpha) version 0.07.

# A Warning

This is very experimental code: use at your own risk.  For certain
there are many cases left unhandled, but it's fresh-baked code after
all.

# Overview

What it says on the tin.  Initially, only eta-reduction and
beta-reduction of simple values (e.g. `(lam x. M) N` where N is a
value in an obvious sense (variable or constant)).  Meant to be used as
cleanup after code generation, typically for human perusal (the
assumption is that compilers will do all the simplifying themselves,
but for humans, it might help for debugging to get ride of all the
superfluous redexes (assuming it's done ... *correctly*).

# Example

Suppose we have a file `test1.ml` (yes, the pattern `P` is nonsensical):
```
value preeq_bdd_node x y =
  match (x, y) with [
    P →
      (fun (x : bdd) (y : bdd) → x == y) x_1 y_1 &&
    (fun (x : bdd) (y : bdd) → x == y) x_2 y_2 && True ]
;

value (hash_attributes_node : attributes_node -> int) =
  fun x ->
    (fun f x ->
       match x with [
         Ploc.VaAnt s -> Hashtbl.hash s
       | Ploc.VaVal v -> f v ])
          hash_attributes_no_anti x ;
```
and we invoke the simplifier:
```
not-ocamlfind preprocess -package camlp5,camlp5.pr_r,pa_ppx_simplify -syntax camlp5r test1.ml
```
we'll get as output
```
value preeq_bdd_node x y =
  match (x, y) with [ P → x_1 == y_1 && x_2 == y_2 && True ]
;

value hash_attributes_node : attributes_node → int =
  fun x →
    match x with
    [ Ploc.VaAnt s → Hashtbl.hash s
    | Ploc.VaVal v → hash_attributes_no_anti v ]
;
```
