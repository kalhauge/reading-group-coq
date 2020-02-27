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

Definition step (exp : term) : option term :=
  match exp with
  | app t1 t2 => 
      match t1 with
      | lambda s _ tm => 
          Some (subst s t2 tm)
      | _ => None
      end
  | a => Some a 
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

*)

Inductive typesto : list (string * type) -> term -> type -> Prop :=
| intro_bool : forall L b, typesto L (const b) B
| intro_var : forall L v t, In (v, t) L -> typesto L (var v) t
| intro_app : forall L e1 e2 t1 t2, 
    typesto L e1 (arr t1 t2)
    -> typesto L e2 t2
    -> typesto L (app e1 e2) t2
.

Theorem progress : forall L e t, typesto L e t -> exists e', step e = Some e'.
Proof.
  intros.
  induction H.
  - refine (ex_intro _ (const b) _).
    reflexivity.
  - now exists (var v).
  - 
Qed.






