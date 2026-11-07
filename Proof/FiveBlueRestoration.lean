import FiveRedRestoration
namespace JSP452Audit.StarHost.FiveExposurePorts
open SimpleGraph
variable {X : Type*} [Finite X] {G : SimpleGraph X} (s : FiveExposurePorts G)
variable {Z : Type*} [Finite Z]

theorem high_blue_center (J : SimpleGraph (s.U⊕Z)) (R : SimpleGraph (X⊕(s.U⊕Z)))
    (blueCap : ∀v,Nat.card (((s.auxiliary J) \ R).neighborSet v)≤2)
    (A B : Set s.U) (partition : A∪B=s.marked R) (x:X)
    (high : 2<Nat.card ((G \ s.restoredRed R B).neighborSet x)) : x∈Subtype.val '' B := by
  classical
  by_contra away
  have bound := s.degree_through_lift (G \ s.restoredRed R B) ((s.auxiliary J) \ R) x ∅ (by
    intro y edge _
    have orig : G.Adj x y := edge.1
    have no : ¬(s.M.Adj x y ∨ R.Adj (.inl x) (.inl y) ∨ s.chosenAt Bᶜ x y) := edge.2
    by_cases back : ∃u:s.U,u.val=y ∧ s.target u=x
    · obtain ⟨u,uy,ux⟩ := back
      have markB : u∈B := by
        by_contra notB
        exact no (Or.inr (Or.inr ⟨u,notB,Or.inr ⟨uy,ux⟩⟩))
      have mark : u∈s.marked R := partition ▸ (show u∈A∪B from Or.inr markB)
      subst x;subst y
      rw [s.lift_at_target]
      exact ⟨rfl,mark⟩
    · rw [s.lift_else back]
      have kept : s.kept x y := by
        refine ⟨orig,fun m => no (Or.inl m),?_⟩
        rintro ⟨u,_,choices⟩
        rcases choices with ⟨ux,uy⟩|⟨uy,ux⟩
        · have notB : u∉B := fun ub => away ⟨u,ub,ux⟩
          exact no (Or.inr (Or.inr ⟨u,notB,Or.inl ⟨ux,uy⟩⟩))
        · exact back ⟨u,uy,ux⟩
      exact ⟨kept,fun e => no (Or.inr (Or.inl e))⟩)
  rw [Set.ncard_empty,Nat.add_zero] at bound
  have cap := blueCap (.inl x)
  omega

/-- Every auxiliary two/two split has at least p+q−1 of the true exposed
labels on either chosen port color. -/
theorem marked_labels_cover_width (J : SimpleGraph (s.U⊕Z)) (R : SimpleGraph (X⊕(s.U⊕Z)))
    (sub : R≤s.auxiliary J) (caps : ∀v,Nat.card (R.neighborSet v)≤2 ∧
      Nat.card (((s.auxiliary J) \ R).neighborSet v)≤2)
    (p q : ℕ) (hp : 0<p) (hq : 0<q)
    (forced : Forces G (forest (fun _ : Fin p => 4)) (forest (fun _ : Fin q => 3))) :
    p+q-1≤(s.marked R).ncard := by
  classical
  by_contra! small
  obtain ⟨A,B,part,_,red,blue⟩ := split_control_budget (s.marked R) hp hq small
  let C := s.restoredRed R B
  rcases forced C (s.restoredRed_le J R sub B) with h|h
  · have bound := count_large_of_center_cover C (s.target '' A) 3 (fun _ : Fin p => 4)
      (s.high_red_center J R sub (fun v => (caps v).1) A B part) h
    have count := Set.ncard_image_le (f:=s.target) (s:=A)
    simp only [Nat.reduceAdd,le_refl,Finset.filter_true,Finset.card_univ,Fintype.card_fin] at bound
    omega
  · have bound := count_large_of_center_cover (G \ C) (Subtype.val '' B) 2 (fun _ : Fin q => 3)
      (s.high_blue_center J R (fun v => (caps v).2) A B part) h
    have count := Set.ncard_image_le (f:=Subtype.val) (s:=B)
    simp only [Nat.reduceAdd,le_refl,Finset.filter_true,Finset.card_univ,Fintype.card_fin] at bound
    omega

theorem marked_complement (J : SimpleGraph (s.U⊕Z)) (R : SimpleGraph (X⊕(s.U⊕Z))) :
    s.marked (s.auxiliary J \ R)=(s.marked R)ᶜ := by
  classical
  ext u
  change (¬((s.auxiliary J).Adj (.inl (s.target u)) (.inr (.inl u)) ∧ ¬R.Adj _ _)) ↔ ¬¬R.Adj _ _
  have port : (s.auxiliary J).Adj (.inl (s.target u)) (.inr (.inl u)) := rfl
  tauto

theorem both_port_colours_pay (J : SimpleGraph (s.U⊕Z)) (R : SimpleGraph (X⊕(s.U⊕Z)))
    (sub : R≤s.auxiliary J) (caps : ∀v,Nat.card (R.neighborSet v)≤2 ∧ Nat.card (((s.auxiliary J) \ R).neighborSet v)≤2)
    (p q : ℕ) (hp : 0<p) (hq : 0<q)
    (forced : Forces G (forest (fun _ : Fin p => 4)) (forest (fun _ : Fin q => 3))) :
    p+q-1≤(s.marked R).ncard ∧ p+q-1≤(s.marked R)ᶜ.ncard := by
  let H := s.auxiliary J
  have twice : H \ (H \ R)=R := by
    ext x y;change (H.Adj x y ∧ ¬(H.Adj x y ∧ ¬R.Adj x y)) ↔ R.Adj x y
    exact ⟨fun e => Classical.byContradiction (fun no => e.2 ⟨e.1,no⟩),fun r => ⟨sub r,fun e => e.2 r⟩⟩
  refine ⟨s.marked_labels_cover_width J R sub caps p q hp hq forced,?_⟩
  rw [←s.marked_complement J R]
  apply s.marked_labels_cover_width J (H \ R) sdiff_le _ p q hp hq forced
  intro v
  change Nat.card ((H \ R).neighborSet v)≤2 ∧ Nat.card ((H \ (H \ R)).neighborSet v)≤2
  rw [twice];exact ⟨(caps v).2,(caps v).1⟩

#print axioms high_blue_center
#print axioms marked_labels_cover_width
#print axioms both_port_colours_pay
end JSP452Audit.StarHost.FiveExposurePorts
