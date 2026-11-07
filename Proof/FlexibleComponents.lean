import BinaryFlexDef
import FlexibleAlloc

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A real coloring with independent bounds on its two matching numbers. -/
def FitsRankBudgets {X : Type*} [Finite X] (G : SimpleGraph X) (red blue : ℕ) : Prop :=
  ∃ R : SimpleGraph X, R ≤ G ∧ matchingEdges R ≤ red ∧ matchingEdges (G \ R) ≤ blue

private theorem fits_iso {X Y : Type*} [Finite X] [Finite Y] {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : G ≃g H) {r b : ℕ} (fit : FitsRankBudgets G r b) : FitsRankBudgets H r b := by
  obtain ⟨R,sub,red,blue⟩ := fit
  let K := R.comap e.symm
  refine ⟨K,fun x y h => e.symm.map_rel_iff.mp (sub h),?_,?_⟩
  · exact (rank_eq_of_graph_iso (Iso.comap e.symm.toEquiv R)).le.trans red
  · have eq : H \ K = (G \ R).comap e.symm := by
      ext x y
      change (H.Adj x y ∧ ¬R.Adj (e.symm x) (e.symm y)) ↔
        (G.Adj (e.symm x) (e.symm y) ∧ ¬R.Adj (e.symm x) (e.symm y))
      rw [e.symm.map_rel_iff]
    rw [eq]
    exact (rank_eq_of_graph_iso (Iso.comap e.symm.toEquiv (G \ R))).le.trans blue

private theorem fits_sum {X Y : Type*} [Finite X] [Finite Y] {G : SimpleGraph X} {H : SimpleGraph Y}
    {r₁ r₂ b₁ b₂ : ℕ} (f : FitsRankBudgets G r₁ b₁) (g : FitsRankBudgets H r₂ b₂) :
    FitsRankBudgets (G ⊕g H) (r₁+r₂) (b₁+b₂) := by
  obtain ⟨A,a,ar,ab⟩ := f
  obtain ⟨B,b,br,bb⟩ := g
  have sub : A ⊕g B ≤ G ⊕g H := by
    rintro (x|x) (y|y) h
    · exact a h
    · exact (not_adj_sum_inl_inr _ _ h).elim
    · exact (not_adj_sum_inl_inr _ _ h.symm).elim
    · exact b h
  have comp : (G ⊕g H) \ (A ⊕g B) = (G \ A) ⊕g (H \ B) := by
    ext x y; rcases x with x|x <;> rcases y with y|y <;> simp
  refine ⟨A ⊕g B,sub,?_,?_⟩
  · rw [matchingEdges_sumGraph]; exact Nat.add_le_add ar br
  · rw [comp,matchingEdges_sumGraph]; exact Nat.add_le_add ab bb

private def componentLabels {X : Type*} (G : SimpleGraph X) (T : Finset G.ConnectedComponent) :
    Set X := {x | G.connectedComponentMk x ∈ T}

/-- Every local coloring is made on the original labeled host after transport.
At the same time the total matching number is exactly the component sum. -/
theorem component_rank_budget_gluing {X : Type*} [Finite X] (G : SimpleGraph X)
    [Fintype G.ConnectedComponent] :
    matchingEdges G = ∑ c : G.ConnectedComponent, matchingEdges c.toSimpleGraph ∧
    ∀ r b : G.ConnectedComponent → ℕ, (∀ c, FitsRankBudgets c.toSimpleGraph (r c) (b c)) →
      FitsRankBudgets G (∑ c, r c) (∑ c, b c) := by
  classical
  have claim (T : Finset G.ConnectedComponent) :
      matchingEdges (G.induce (componentLabels G T)) = ∑ c ∈ T,matchingEdges c.toSimpleGraph ∧
      ∀ r b : G.ConnectedComponent → ℕ, (∀ c, FitsRankBudgets c.toSimpleGraph (r c) (b c)) →
        FitsRankBudgets (G.induce (componentLabels G T)) (∑ c ∈ T,r c) (∑ c ∈ T,b c) := by
    induction T using Finset.induction_on with
    | empty =>
      have empty : G.induce (componentLabels G ∅) = ⊥ := by
        ext x; exact (Finset.notMem_empty _ x.property).elim
      simp only [empty,matchingEdges_bot,Finset.sum_empty,true_and]
      intro r b _
      exact ⟨⊥,le_rfl,by simp [matchingEdges_bot],by simp [matchingEdges_bot]⟩
    | @insert c T fresh ih =>
      have cover : c.supp ∪ componentLabels G T = componentLabels G (insert c T) := by
        ext x; exact Finset.mem_insert.symm
      have dis : Disjoint c.supp (componentLabels G T) := Set.disjoint_left.mpr (by
        intro x hx ht; exact fresh ((show G.connectedComponentMk x = c from hx) ▸ ht))
      have sep : ∀ x∈c.supp, ∀ y∈componentLabels G T, ¬G.Adj x y :=
        fun _ hx _ hy edge => Set.disjoint_left.mp dis ((c.mem_supp_congr_adj edge).mp hx) hy
      let e := regionSumIso G _ _ _ cover dis sep
      refine ⟨?_,?_⟩
      · rw [← rank_eq_of_graph_iso e,matchingEdges_sumGraph,ih.1,Finset.sum_insert fresh]
        rfl
      · intro r b localFits
        rw [Finset.sum_insert fresh,Finset.sum_insert fresh]
        exact fits_iso e (fits_sum (localFits c) (ih.2 r b localFits))
  have all : componentLabels G Finset.univ = Set.univ := by ext; simp [componentLabels]
  obtain ⟨card,glue⟩ := claim Finset.univ
  rw [all] at card glue
  rw [rank_eq_of_graph_iso (induceUnivIso G)] at card
  exact ⟨card,fun r b localFits => fits_iso (induceUnivIso G) (glue r b localFits)⟩


/-- Flexible components absorb every leftover allowance, while each rigid
component is given one color in its entirety. -/
theorem exactRankSplit_of_flexible {X : Type*} [Finite X] (G : SimpleGraph X)
    (ready : ∀ c, pathLike G c → ExactRankSplit c.toSimpleGraph)
    (small : ∀ c : G.ConnectedComponent, matchingEdges c.toSimpleGraph ≤ 3)
    (ample : 2 ≤ pathCapacity G) : ExactRankSplit G := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  let z (c : G.ConnectedComponent) := matchingEdges c.toSimpleGraph
  obtain ⟨total,piecewise⟩ := component_rank_budget_gluing G
  intro u hu
  have room : u ≤ ∑ c, z c := hu.trans_eq total
  obtain ⟨r,lim,whole,used⟩ := flexible_allocation z (pathLike G) small ample u room
  let b (c : G.ConnectedComponent) := z c-r c
  have localFits (c : G.ConnectedComponent) : FitsRankBudgets c.toSimpleGraph (r c) (b c) := by
    by_cases flex : pathLike G c
    · exact ready c flex (r c) (lim c)
    rcases whole c flex with left | right
    · refine ⟨⊥,bot_le,?_,?_⟩
      · simp [matchingEdges_bot]
      · simp only [b,left,Nat.sub_zero,sdiff_bot,le_refl,z]
    · refine ⟨c.toSimpleGraph,le_rfl,?_,?_⟩
      · exact right.ge
      · simp [matchingEdges_bot]
  have count : (∑ c, r c) + (∑ c, b c) = ∑ c, z c := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => by dsimp only [b]; have h := lim c; omega)
  have sumBlue : (∑ c, b c) = matchingEdges G-u := by
    change matchingEdges G = ∑ c,z c at total
    omega
  have color := piecewise r b localFits
  rwa [used,sumBlue] at color

#print axioms exactRankSplit_of_flexible

#print axioms component_rank_budget_gluing
end JSP452Audit.StarHost
