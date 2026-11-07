import DetachedPairLabels
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Exact four-regular boundary prices for the two actual separated odd parts. -/
theorem four_detached_pair_exact_prices (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (reg : ∀v,Nat.card (Q.neighborSet v)=4)
    (s : DetachedMatePair (Q.induce Iᶜ)) (count : s.singles.ncard+3=I.ncard) :
    let P := Subtype.val '' s.preferred
    let C := Subtype.val '' s.companion
    C.ncard=3 ∧ crossCount Q C Cᶜ=6 ∧ crossCount Q P Pᶜ=6 ∧
      (P.ncard=5 ∨ P.ncard=3 ∧ Q.IsClique P) := by
  intro P C
  let D : ℕ := 4
  classical
  let F : Fin 3→Set ↥(Iᶜ : Set X) := fun i => if i=0 then s.singles else if i=1 then s.preferred else s.companion
  let A (i:Fin 3) : Set X := Subtype.val '' F i
  have dis (i j:Fin 3) (ne:i≠j) : Disjoint (F i) (F j) := by
    fin_cases i <;> fin_cases j <;> simp_all [F,s.apart,s.apart.symm,s.sp,s.sp.symm,s.sc,s.sc.symm]
  have sep (i j:Fin 3) (ne:i≠j) : ∀a∈F i,∀b∈F j,¬(Q.induce Iᶜ).Adj a b := by
    intro a ha b hb edge
    fin_cases i <;> fin_cases j <;> simp_all [F] <;>
      first
      | exact s.isolated a ha b edge
      | exact s.isolated b hb a edge.symm
      | exact s.apart_edges a ha b hb edge
      | exact s.apart_edges b hb a ha edge.symm
  have cover (v : ↥(Iᶜ : Set X)) : ∃i,v∈F i := by
    rcases s.cover v with hs|hc|hp
    · exact ⟨0,hs⟩
    · exact ⟨2,hc⟩
    · exact ⟨1,hp⟩
  have external (i : Fin 3) (v:X) (hv:v∈A i) (w:X) (edge:Q.Adj v w) (out:w∉A i) : w∈I := by
    by_contra away
    obtain ⟨a,ha,rfl⟩ := hv
    let t : ↥(Iᶜ : Set X) := ⟨w,away⟩
    obtain ⟨j,hj⟩ := cover t
    exact sep i j (fun eq => out ⟨t,eq.symm ▸ hj,rfl⟩) a ha t hj edge
  have budget := disjoint_cut_total_budget Q A I D
    (fun i j ne => Set.disjoint_image_of_injective Subtype.val_injective (dis i j ne))
    external (fun x _ => (reg x).le)
  have singles : crossCount Q (A 0) (A 0)ᶜ=s.singles.ncard*D := by
    have f := uniform_cross_count Q (A 0) (A 0)ᶜ D (by
      rintro _ ⟨v,hv,rfl⟩
      have sub : Q.neighborSet v.val⊆(A 0)ᶜ := by
        rintro y adj ⟨w,hw,rfl⟩
        exact s.isolated v hv w adj
      rw [Set.inter_eq_left.mpr sub,←Nat.card_coe_set_eq,reg])
    rw [crossCount_swap] at f
    exact f.trans (congrArg (fun n:ℕ => n*D) (Set.ncard_image_of_injective _ Subtype.val_injective))
  have sum (f:Fin 3→ℕ) : (∑i,f i)=f 0+(f 1+f 2) := by
    rw [show (Finset.univ : Finset (Fin 3))={0,1,2} by decide]; simp
  rw [sum,singles,←count,Nat.add_mul] at budget
  change s.singles.ncard*D+(crossCount Q P Pᶜ+crossCount Q C Cᶜ)≤s.singles.ncard*D+3*D at budget
  have balance := Nat.le_of_add_le_add_left budget
  have pcard : P.ncard=s.preferred.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have ccard : C.ncard=s.companion.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have cl : Q.IsClique C := by
    rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne
    exact s.companion_clique hv hw (fun eq => ne (congrArg Subtype.val eq))
  have cOutside : C⊆Iᶜ := by rintro _ ⟨v,_,rfl⟩;exact v.property
  have pOutside : P⊆Iᶜ := by rintro _ ⟨v,_,rfl⟩;exact v.property
  have dc := outside_largest_clique_size Q I C ind largest cOutside cl D (fun v => (reg v).le)
  have deg : D=4 := rfl
  have oc : Odd C.ncard := ccard.symm ▸ s.companion_odd
  have cop := Nat.odd_iff.mp oc
  have clo : 3≤C.ncard := ccard.symm ▸ s.companion_big
  have chi : C.ncard≤D-1 := by omega
  have qc := clique_boundary_count Q C D cl (fun v _ => reg v)
  have c3 : C.ncard=3 := by omega
  have c6 : crossCount Q C Cᶜ=6 := by rw [qc,c3,deg]
  have upP : crossCount Q P Pᶜ≤6 := by omega
  have lower := boundary_at_least_region_order Q I P ind largest pOutside
  have op : Odd P.ncard := pcard.symm ▸ s.preferred_odd
  have pp := Nat.odd_iff.mp op
  have plo : 3≤P.ncard := pcard.symm ▸ s.preferred_big
  have sizes : P.ncard=5 ∨ P.ncard=3 := by omega
  have actual := small_region_boundary_missing Q P 4 (fun v _ => reg v) (by omega)
  refine ⟨c3,c6,?_,?_⟩
  · rcases sizes with h|h <;> rw [h] at actual <;> omega
  · rcases sizes with h|h
    · exact Or.inl h
    right;refine ⟨h,?_⟩
    rw [h] at actual
    have empty : (Q.induce P)ᶜ.edgeSet=∅ := (Set.ncard_eq_zero (s := (Q.induce P)ᶜ.edgeSet)).mp (show (Q.induce P)ᶜ.edgeSet.ncard=0 by omega)
    intro a ha b hb ne
    by_contra bad
    have edge : s((⟨a,ha⟩:P),(⟨b,hb⟩:P))∈(Q.induce P)ᶜ.edgeSet :=
      ⟨fun eq => ne (congrArg Subtype.val eq),bad⟩
    rwa [empty] at edge

#print axioms four_detached_pair_exact_prices
end JSP452Audit.StarHost
