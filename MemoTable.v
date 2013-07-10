Require Import RGref.DSL.DSL.
Require Import Coq.Arith.Arith.

Section MemoTable.

  (* Apparently the instances below stick around after the section ends... *)
  Variable B : nat -> Set.
  Variable f : forall (x:nat), B x.
  Parameter safe_f : Safe f.
  Existing Instance safe_f.
  Parameter safe_B : Safe B.
  Existing Instance safe_B.

  Definition prefernat {P:nat->Set}(g:forall x:nat, P x)(a:nat) : forall x:nat, P x.
    refine(let v := g a in
             (fun x => if eq_nat_dec x a then _ else g x)).
    subst. exact v.
  Defined.
  Print prefernat.

  Definition obs_equiv {A:Set}{P:A->Set}(f g:forall x, P x)(_ _:heap) :=
    forall x, f x = g x.
  Lemma obs_eq_refl : forall A P, hreflexive (@obs_equiv A P).
  Proof. intros; red. compute. eauto. Qed.
  Hint Resolve obs_eq_refl.
  Lemma precise_obs_equiv : precise_rel (@obs_equiv nat (fun _ => nat)).
  Proof. compute. intuition. Qed.
  Hint Resolve precise_obs_equiv.

  Instance safe_prefernat : Safe (@prefernat).
(*  Instance prior_safe (r:ref{forall x:nat,B x|any}[obs_equiv,obs_equiv]) (n:nat)
    : Safe (@prefernat B (@deref _ _ _ _ _ _ (obs_eq_refl _ _) eq_refl r) n). *)
  Instance prior_safe (r:ref{forall x:nat,B x|any}[obs_equiv,obs_equiv]) (n:nat)
                              : ESafe 0 (@prefernat B f n).
    repeat solve_applications.
  Defined.
    
  Program Definition prioritize {Γ} (r:ref{forall x:nat,B x|any}[obs_equiv,obs_equiv]) (n:nat) : rgref Γ unit Γ :=
    [r]:= prefernat (!r) n.
  Next Obligation.
    repeat solve_applications.
  Qed.
  Next Obligation.
    red. unfold prefernat. intros. induction (eq_nat_dec x n); intuition; eauto.
    subst. compute. eauto.
  Qed.
(* Doesn't (and shouldn't!) typecheck *)
  Program Example should_not_typecheck {Γ} (r:ref{nat|any}[havoc,havoc]) : rgref Γ (ref{nat->nat|any}[havoc,havoc]) Γ :=
    Alloc (fun x => !r). (*;
    prioritize _ r 0.
  (*Print should_not_typecheck.*)
*)
  Next Obligation. compute; eauto. Defined.
  Next Obligation.
    (* Cannot typecheck because (λ x:N. !r) is in fact not safe! *)
  Admitted.

End MemoTable.