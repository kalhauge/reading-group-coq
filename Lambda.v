Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Inductive type : Type :=
| arr : type -> type -> type
| B : type.

Inductive term : Type :=
| lambda : string -> type -> term -> term
| var : string -> term
| app : term -> term -> term
| const : bool -> term
.

Definition idB : term := lambda "x" B (var "x").

Fixpoint subst (n : string) (nt : term) (exp: term) : term :=
  match exp with
  | lambda s t tm => 
      if eqb n s 
      then lambda s t tm
      else lambda s t (subst n nt tm)
  | var s => 
      if eqb n s 
      then nt
      else var s
  | app t1 t2 => 
      app (subst n nt t1) (subst n nt t2)
  | const b => 
      const b
  end.

Theorem simple_const : subst "x" (const true) (var "x") = const true.
Proof.
  simpl.
  reflexivity.
Qed.

Definition is_value (exp : term) : bool :=
  match exp with
  | app _ _ => false
  | var _   => false
  | _       => true
  end.

Fixpoint step (exp : term) : option term :=
  match exp with
  | app t1 t2 => 
      if is_value t1 
      then match t1 with
      | lambda s _ tm => 
          Some (subst s t2 tm)
      | _ => None
      end
      else option_map (fun t1' => app t1' t2) (step t1)
  | _ => None
  end.

Compute step (app idB (const true)).

Theorem step_id : forall e, (step (app idB e) = Some e).
Proof.
  intros.
  simpl.
  apply eq_refl.
Qed.

(* 
----------------  [intro_bool]
L |- const b : B 

 (v, t) in L
----------------  [intro_var]
 L |- v : t
 
 L |- e1 : t1 -> t2
 L |- e2 : t1 
----------------  [intro_app]
 L |- e1 e2 : t2
 
 (v,t),L |- e : t2 
-----------------------  [intro_lam]
 L |- lambda v : t. e : t -> t2

*)

Inductive firstIn (s : string) (t : type) : list (string * type) -> Prop :=
| fFirst : forall l, firstIn s t (cons (s,t) l) 
| fDeeper : forall s' t2 l, 
    s' <> s 
    -> firstIn s t l
    -> firstIn s t (cons (s',t2) l) 
.


Inductive typesto : list (string * type) -> term -> type -> Prop :=
| intro_bool : forall L b, 
    typesto L (const b) B
| intro_var : forall L v t, 
    firstIn v t L 
    -> typesto L (var v) t
| intro_app : forall L e1 e2 t1 t2, 
    typesto L e1 (arr t1 t2)
    -> typesto L e2 t2
    -> typesto L (app e1 e2) t2
| intro_lam : forall L v e t t2, 
    typesto (cons (v,t) L) e t2
    -> typesto L (lambda v t e) (arr t t2)
.

Lemma only_lambda_is_value : forall e L t1 t2 , 
  is_value e = true 
  -> typesto L e (arr t1 t2)
  -> exists s' t' e', e = lambda s' t' e'.
Proof.
  intros.
  inversion H0.
  - rewrite <- H3 in H.
    inversion H.
  - rewrite <- H4 in H. inversion H.
  - exists v, t1, e0. easy.
Qed.

Theorem progress : forall L e t, 
  typesto L e t 
  -> L = nil
  -> is_value e = true \/ exists e', step e = Some e'.
Proof.
  intros.
  induction H.
  - left; reflexivity.
  - right.
    rewrite H0 in H.
    inversion H.
  - right.
    apply IHtypesto1 in H0.
    inversion H0.
    inversion IHtypesto1.
  
  refine (ex_intro _ (const b) _).
    reflexivity.
  - now exists (var v).
  - 
Qed.






