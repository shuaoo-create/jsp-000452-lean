import FivePortDegreeCount
namespace JSP452Audit.StarHost.FiveExposurePorts
open SimpleGraph
variable {X : Type*} [Finite X] {G : SimpleGraph X} (s : FiveExposurePorts G)
variable {Z : Type*} [Finite Z]

def marked (R : SimpleGraph (X⊕(s.U⊕Z))) : Set s.U :=
  {u | ¬R.Adj (.inl (s.target u)) (.inr (.inl u))}

theorem chosen_original {A : Set s.U} {x y : X} (edge : s.chosenAt A x y) : G.Adj x y := by
  obtain ⟨u,_,h⟩ := edge
  rcases h with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact h1 ▸ h2 ▸ s.link u
  · exact h1 ▸ h2 ▸ (s.link u).symm

def restoredRed (R : SimpleGraph (X⊕(s.U⊕Z))) (B : Set s.U) : SimpleGraph X where
  Adj x y := s.M.Adj x y ∨ R.Adj (.inl x) (.inl y) ∨ s.chosenAt Bᶜ x y
  symm := ⟨fun x y h => h.elim (fun e => Or.inl e.symm)
    (fun e => Or.inr (e.imp (fun z => z.symm) (s.chosen_symm _ x y)))⟩
  loopless := ⟨fun x h => h.elim (fun e => G.irrefl (s.M.adj_sub e))
    (fun e => e.elim (fun z => R.irrefl z) (fun z => G.irrefl (s.chosen_original z)))⟩

theorem restoredRed_le (J : SimpleGraph (s.U⊕Z)) (R : SimpleGraph (X⊕(s.U⊕Z))) (sub : R≤s.auxiliary J)
    (B : Set s.U) : s.restoredRed R B≤G := by
  intro x y h
  rcases h with e|e|e
  · exact s.M.adj_sub e
  · exact (show s.kept x y from sub e).1
  · exact s.chosen_original e

theorem lift_at_target (u:s.U) :
    s.liftNeighbor (Z:=Z) (s.target u) u.val=.inr (.inl u) := by
  classical
  simp [liftNeighbor,u.property]

theorem lift_else {x y:X} (absent : ¬∃u:s.U,u.val=y ∧ s.target u=x) :
    s.liftNeighbor (Z:=Z) x y=.inl y := by
  classical
  by_cases hy:y∈s.U
  · have no : s.target ⟨y,hy⟩≠x := fun e => absent ⟨⟨y,hy⟩,rfl,e⟩
    simp [liftNeighbor,hy,no]
  · simp [liftNeighbor,hy]

def spare (x:X) : Set X := {y | s.M.Adj x y ∨ ∃u:s.U,u.val=x ∧ s.target u=y}

theorem spare_size (x:X) : (s.spare x).ncard≤1 := by
  apply (Set.ncard_le_one (Set.toFinite _)).mpr
  intro y hy z hz
  rcases hy with me|⟨u,hx,hy⟩ <;> rcases hz with other|⟨v,vx,vz⟩
  · exact s.matching.eq_of_adj_left me other
  · exact (s.missed v (vx.symm ▸ s.M.edge_vert me)).elim
  · exact (s.missed u (hx.symm ▸ s.M.edge_vert other)).elim
  · have same : u=v := Subtype.ext (hx.trans vx.symm)
    exact hy.symm.trans ((congrArg s.target same).trans vz)

theorem degree_through_lift (Q : SimpleGraph X) (R : SimpleGraph (X⊕(s.U⊕Z)))
    (x:X) (E:Set X) (transfer : ∀y,Q.Adj x y → y∉E → R.Adj (.inl x) (s.liftNeighbor x y)) :
    Nat.card (Q.neighborSet x)≤Nat.card (R.neighborSet (.inl x))+E.ncard := by
  let P := Q.neighborSet x\E
  let f (v:P) : R.neighborSet (.inl x) := ⟨s.liftNeighbor x v.val,transfer v.val v.property.1 v.property.2⟩
  have inj : Function.Injective f := by
    intro a b eq
    exact Subtype.ext (s.lift_injective x (congrArg (fun z : R.neighborSet (.inl x) => z.val) eq))
  have upper := Nat.card_le_card_of_injective f inj
  rw [Nat.card_coe_set_eq (s:=P)] at upper
  have sub : Q.neighborSet x⊆P∪E := by
    intro y adj;by_cases mem : y∈E
    · exact Or.inr mem
    · exact Or.inl ⟨adj,mem⟩
  have count := (Set.ncard_le_ncard sub).trans (Set.ncard_union_le P E)
  rw [Nat.card_coe_set_eq (s:=Q.neighborSet x)]
  omega

/-- Any original red degree-four center must be the other endpoint of a
marked edge assigned red, even when many labels share that endpoint. -/
theorem high_red_center (J : SimpleGraph (s.U⊕Z)) (R : SimpleGraph (X⊕(s.U⊕Z)))
    (sub : R≤s.auxiliary J) (redCap : ∀v,Nat.card (R.neighborSet v)≤2)
    (A B : Set s.U) (partition : A∪B=s.marked R) (x:X)
    (high : 3<Nat.card ((s.restoredRed R B).neighborSet x)) : x∈s.target '' A := by
  classical
  by_contra away
  have bound := s.degree_through_lift (s.restoredRed R B) R x (s.spare x) (by
    intro y edge fresh
    rcases edge with mate|old|picked
    · exact (fresh (Or.inl mate)).elim
    · have kept : s.kept x y := sub old
      have no : ¬∃u:s.U,u.val=y ∧ s.target u=x := by
        rintro ⟨u,uy,ux⟩;exact kept.2.2 ⟨u,Set.mem_univ _,Or.inr ⟨uy,ux⟩⟩
      rw [s.lift_else no];exact old
    · obtain ⟨u,notB,choices⟩ := picked
      rcases choices with ⟨ux,uy⟩|⟨uy,ux⟩
      · exact (fresh (Or.inr ⟨u,ux,uy⟩)).elim
      have red : R.Adj (.inl (s.target u)) (.inr (.inl u)) := by
        by_contra no
        have mark : u∈s.marked R := no
        have inside : u∈A∪B := partition.symm ▸ mark
        exact away ⟨u,inside.resolve_right notB,ux⟩
      subst x;subst y
      rw [s.lift_at_target];exact red)
  have spare := s.spare_size x
  have cap := redCap (.inl x)
  omega

#print axioms restoredRed_le
#print axioms high_red_center
end JSP452Audit.StarHost.FiveExposurePorts
