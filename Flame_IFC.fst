(*--build-config 
  options:--admit_fsi FStar.Set --admit_fsi Flame.FLAM ;
  other-files: set.fsi Flame_FLAM.fst;
--*)
module Flame.IFC

open Flame.FLAM

open FStar.All
open FStar.ST
open FStar.Set

kind IFCPre (context:Type) = STPre_h context
kind IFCPost (context:Type) (a:Type) = STPost_h context a

type IFC (context:Type) (a:Type) (pre:IFCPre context) (post: (context -> IFCPost context a)) =
  ctx0:context -> Pure (a * context) (pre ctx0) (fun actx -> post (snd actx) (fst actx) ctx0)

type c_rec = (tc:trust_config * pc:prin)
type c_pre (tc:trust_config) = (fun crec -> subset tc (fst crec) == true)
type c_post (#a:Type) (tc:trust_config) (pc:prin) = 
  (fun crec0 (x:a) crec1 -> subset tc (fst crec0) /\ flowsto tc (snd crec0) pc)
type C (tc:trust_config) (pc:prin) (a:Type) = IFC c_rec a (c_pre tc) (c_post tc pc)

type t_rec = {tc:trust_config; pc:prin; lbl:prin}
type t_pre (tc:trust_config) (pc:prin) = 
  (fun trec -> subset tc trec.tc /\ flowsto tc trec.pc pc)
type t_post (#a:Type) (tc:trust_config) (pc:prin) (lbl:prin) = 
  (fun trec0 (x:a) trec1 -> subset tc trec0.tc /\ flowsto tc trec0.pc pc /\ flowsto tc trec0.lbl lbl)
type T (tc:trust_config) (pc:prin) (lbl:prin) (a:Type) = IFC t_rec a (t_pre tc pc) (t_post tc pc lbl)

type P (tc:trust_config) (a:Type) = 
  IFC trust_config a (fun tc' -> subset tc tc' == true) (fun tc0 x tc1 -> subset tc tc0 == true)

type M (tc:trust_config) (pc:prin) (l:prin) (a:Type) = P tc (C tc pc (T tc pc l a)) 
val t_return : #a:Type -> tc:trust_config -> pc:prin -> l:prin -> x:a -> Tot (T tc pc l a)
let t_return (#a:Type) tc pc l x l0 = (x, {tc=tc;pc=pc;lbl=l})

val c_return : #a:Type -> tc:trust_config -> pc:prin -> #l:prin -> x:T tc pc l a -> Tot (C tc pc (T tc pc l a))
let c_return (#a:Type) tc pc l x pc0 = (x, (tc,pc))

val p_return : #a:Type -> tc:trust_config -> #pc:prin -> #l:prin -> x:C tc pc (T tc pc l a) -> Tot (P tc (C tc pc (T tc pc l a)))
let p_return (#a:Type) tc pc l x l0 = (x, tc)

val return : #a:Type -> tc:trust_config -> pc:prin -> l:prin -> x:a -> Tot (M tc pc l a)
let return (#a:Type) tc pc l x = p_return tc (c_return tc pc (t_return tc pc l x))

type A (p:prin) (q:prin) = 
  IFC (prin * prin) unit (fun pq -> p==(fst pq) /\ q==(snd pq)) (fun pq0 x pq1 -> p==(fst pq0) /\ q==(snd pq0))
val del : p:prin -> q:prin -> Tot (A p q) 
let del p q _ = ((), (p, q)) 

assume val t_bind : #a:Type -> #b:Type -> #tc:trust_config -> #pc:prin -> #l:prin -> #l':prin
            -> f:T tc pc l a{flowsto tc (join pc l) l'}
            -> g: (x:a -> Tot (T tc pc l' b))
            -> Tot (T tc pc l' b)

assume val c_bind : #a:Type -> #b:Type -> #tc:trust_config -> #pc:prin -> #pc':prin
            -> f:C tc pc a{flowsto tc pc pc'}
            -> g: (x:a -> Tot (C tc pc' b))
            -> Tot (C tc pc b)

assume val p_bind : #a:Type -> #b:Type -> #tc:trust_config -> #tc':trust_config 
            -> f:P tc a
            -> g: (x:a -> Tot (P tc b))
            -> Tot (P tc b)

assume val bind : #a:Type -> #b:Type -> #tc:trust_config -> #pc:prin -> #l:prin 
            -> #pc':prin
	    -> #l':prin
            -> f:M tc pc l a
            -> g: (x:a -> Tot (M tc pc' l' b)){flowsto tc (join pc l) pc' /\ flowsto tc l l'}
            -> Tot (M tc pc l' b)

assume val authorize : #a:Type -> #b:Type -> #tc:trust_config -> #tc':trust_config -> #pc:prin -> #l:prin 
            -> #pc':prin -> #l':prin -> #p:prin -> #q:prin
            -> d:M tc pc l (A p q) 
            -> g:(x:unit -> Tot (M (add tc' (p,q,pc,l)) (join pc l) l' b)){
	     // the premises of FLAC's assume
	     actsfor tc l (voice q)
	     /\  actsfor tc pc (voice q)
	     /\  actsfor tc (voice p) (voice q)
	     /\  flowsto tc l l'}
            -> Tot (M tc pc l' b)

(* sanity checks for return *)
let return_test0 tc pc l x = (return empty pc l x) tc 
//let return_test1 tc pc l x = (p_return tc pc l x) tc 
// any computation can run in a pc' that flows to pc
//let return_test2 tc pc l x (pc':prin{flowsto empty pc' pc}) l' = (return tc pc l x) empty

// negative test: the converse of test2 is not true
//let return_test3 pc l x (pc':prin) l' = (c_return pc (t_return l x)) pc'
// negative test: can't run in a secret pc
//let return_test4 pc l x (pc':prin) l' = (c_return pc (t_return l x)) pc'

(* sanity checks for bind *)
// using a value x raises the pc 
//let bind_test0 tc pc l x = bind (return tc pc l x) (fun y -> return tc (join pc l) l y)

// a public and trusted pc and l can be used in any computation
////let bind_test1 tc pc l x = bind (return tc flow_bot flow_bot x) (fun y -> return tc pc l y)

// a public and trusted pc and l can be used in any computation (applied to bot context)
//let bind_test2 pc l x = bind (*flow_bot flow_bot pc l*) (return flow_bot flow_bot x) (fun y -> return pc l y) flow_bot

// a public and trusted pc with any label l that flows to l' can be used in a computation with any pc' and l'
//let bind_test6 l pc' (l':prin{l =<= l'}) x = bind (*flow_bot l pc' l'*) (return flow_bot l x) (fun y -> return pc' l' y) 

// negative test: flow_top doesn't (necessarily) flow to l
//let bind_test7 pc l x = bind (*flow_bot flow_bot pc l*) (return flow_bot flow_top x) (fun y -> return pc l y)
// negative test: 
//let bind_test8 pc l x = bind (*flow_bot flow_bot pc l*) (return flow_bot flow_bot x) (fun y -> return pc l y) flow_top

//val apply : #a:Type -> #b:Type -> #pc:prin -> #pc':prin
//            -> e:(a -> Tot (C pc' b)){pc =<= pc'}
//            -> e':C pc a
//            -> Tot (C pc b)
//let apply (#a:Type) (#b:Type) (#pc:prin) (#pc':prin) e e' = 
//  c_bind e' (fun x -> e x)
//
//type sum (a:Type) (b:Type) =
//  | L: a -> sum a b
//  | R: b -> sum a b
//
//val case : #a:Type -> #b:Type -> #c:Type -> #pc:prin -> #pc':prin
//	   -> e:(C pc (sum a b)){pc =<= pc'}   
//	   -> left:(a -> Tot (C pc' c))
//	   -> right:(b -> Tot(C pc' c)) -> Tot(C pc c)
//let case (#a:Type) (#b:Type) (#c:Type) (#pc:prin) (#pc':prin) 
//	 // this didn't type-check until I added the refinement to e.  
//	 //  -- why did I need it? (apply didn't require it)
//	 (e:C pc (sum a b){pc =<= pc'}) (left:(a -> Tot (C pc' c))) (right:(b -> Tot(C pc' c))) =
//  c_bind e (fun (x:sum a b) -> match x with | L xa -> left xa | R xb -> right xb)

(* If I could, I would create macros that rewrite:
      use x y z in e
to 
      bind x (fun x' -> bind y 
	    (fun y' -> bind z
	       (fun z' -> (fun x y z -> e) x' y' z')))
and
       c_match e with ...
to
       c_bind e (fun x -> match x with ...)
*)
  
(*
(**
 * Principal equivalence
 *)
Reserved Infix "==" (at level 70, no associativity).

Inductive prinEq : relation Prin :=
    (* Reflexive transitive symmetric closure *)
  | refl:  
  | symm:  forall p q,              q == p -> p == q
  | trans: forall p q r,  p == q -> q == r -> p == r

    (* Lattice commutativity laws *)
  | conjComm: forall p q,                 p ∧ q == q ∧ p
  | disjComm: forall p q,                 p ∨ q == q ∨ p

    (* Lattice associativity laws *)
  | conjAssoc: forall p q r,        (p ∧ q) ∧ r == p ∧ (q ∧ r)
  | disjAssoc: forall p q r,        (p ∨ q) ∨ r == p ∨ (q ∨ r)

    (* Lattice absorption laws *)
  | conjDisjAbsorb: forall p q,     p ∧ (p ∨ q) == p
  | disjConjAbsorb: forall p q,     p ∨ (p ∧ q) == p

    (* Lattice idempotence laws *)
  | conjIdemp: forall p,                  p ∧ p == p
  | disjIdemp: forall p,                  p ∨ p == p

    (* Lattice identity laws *)
  | conjIdent: forall p,                  p ∧ ⊥ == p
  | disjIdent: forall p,                  p ∨ ⊤ == p
  | conjTop:   forall p,                  p ∧ ⊤ == ⊤
  | disjBot:   forall p,                  p ∨ ⊥ == ⊥

    (* Lattice distributivity law *)
  | conjDistDisj:  forall p q r,    p ∧ (q ∨ r) == (p ∧ q) ∨ (p ∧ r)

    (* Authority projections, property 3: distribution over conjunctions *)
  | conjConf:    forall p q,           (p ∧ q)→ == p→ ∧ q→
  | conjInteg:   forall p q,           (p ∧ q)← == p← ∧ q←
  | ownDistConj: forall p q r,        (p ∧ q):r == p:r ∧ q:r

    (* Authority projections, property 4: distribution over disjunctions *)
  | disjConf:    forall p q,           (p ∨ q)→ == p→ ∨ q→
  | disjInteg:   forall p q,           (p ∨ q)← == p← ∨ q←
  | ownDistDisj: forall p q r,        (p ∨ q):r == p:r ∨ q:r

    (* Authority projections, property 5: idempotence *)
  | confIdemp:  forall p,                   p→→ == p→
  | integIdemp: forall p,                   p←← == p←
  | ownIdemp:   forall p q,             (p:q):q == p:q

    (* Basis projections, properties 2-3 *)
  | confInteg:      forall p,                p→← == ⊥
  | integConf:      forall p,                p←→ == ⊥
  | confDisjInteg:  forall p q,          p→ ∨ q← == ⊥

    (* Ownership projections, properties 3-6 *)
  | ownsSelf:    forall p,                  p:p == p
  | ownsBot:     forall p,                  p:⊥ == ⊥
  | conjDistOwn: forall p q r,        p:(q ∧ r) == p:q ∧ p:r
  | disjDistOwn: forall p q r,        p:(q ∨ r) == p:q ∨ p:r

    (* Ownership projections, property 7 *)
  | ownConfAssoc:  forall p q,             p:q→ == (p:q)→
  | ownIntegAssoc: forall p q,             p:q← == (p:q)←

    (* Ownership projections, property 8 *)
  | ownConf:  forall p q,                  p→:q == (p:q)→
  | ownInteg: forall p q,                  p←:q == (p:q)←

    (* Admitted equivalences *)
  | confIntegBasis: forall p,            p→ ∧ p← == p
  | botConf:                                  ⊥→ == ⊥
  | botInteg:                                 ⊥← == ⊥
  | botOwn:         forall p,                ⊥:p == ⊥

    (* Substitutions *)
  | conjSubst:  forall p p' q q', p == p' -> q == q' -> p ∧ q == p' ∧ q'
  | disjSubst:  forall p p' q q', p == p' -> q == q' -> p ∨ q == p' ∨ q'
  | confSubst:  forall p p',      p == p' ->               p→ == p'→
  | integSubst: forall p p',      p == p' ->               p← == p'←
  | ownsSubst:  forall p p' q q', p == p' -> q == q' ->   p:q == p':q'

where "p == q" := (prinEq p q).
*)
