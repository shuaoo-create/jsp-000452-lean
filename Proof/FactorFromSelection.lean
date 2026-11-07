import SelectedDegree

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X]

/-- Keep all common edges, and choose the specified edges on either side of
the symmetric difference. -/
def factorFromSelection (F₀ F₁ : SimpleGraph X)
    (A : Set (F₀ \ F₁).edgeSet) (B : Set (F₁ \ F₀).edgeSet) : SimpleGraph X :=
  F₀ ⊓ F₁ ⊔ selectedGraph (F₀ \ F₁) A ⊔ selectedGraph (F₁ \ F₀) B

/-- Adding one at each oriented endpoint count changes the actual undirected
degree by exactly two at every vertex. Only the old regularity is required. -/
theorem factor_from_selection {H F₀ F₁ : SimpleGraph X} (h₀ : F₀ ≤ H) (h₁ : F₁ ≤ H)
    (a : ℕ) (oldDegree : ∀ v, Nat.card (F₀.neighborSet v) = a)
    (srcO dstO : (F₀ \ F₁).edgeSet → X) (srcN dstN : (F₁ \ F₀).edgeSet → X)
    (orientO : ∀ e, s(srcO e,dstO e) = e.val) (orientN : ∀ e, s(srcN e,dstN e) = e.val)
    (A : Set (F₀ \ F₁).edgeSet) (B : Set (F₁ \ F₀).edgeSet)
    (sources : ∀ v, Nat.card {e // e ∈ A ∧ srcO e = v} +
      Nat.card {e // e ∈ B ∧ srcN e = v} = Nat.card {e // srcO e = v} + 1)
    (dests : ∀ v, Nat.card {e // e ∈ A ∧ dstO e = v} +
      Nat.card {e // e ∈ B ∧ dstN e = v} = Nat.card {e // dstO e = v} + 1) :
    factorFromSelection F₀ F₁ A B ≤ H ∧
      ∀ v, Nat.card ((factorFromSelection F₀ F₁ A B).neighborSet v) = a + 2 := by
  let C := F₀ ⊓ F₁
  let O := F₀ \ F₁
  let N := F₁ \ F₀
  let U := selectedGraph O A
  let V := selectedGraph N B
  have subU : U ≤ O := selectedGraph_le _ _
  have subV : V ≤ N := selectedGraph_le _ _
  have co : Disjoint C O := SimpleGraph.disjoint_left.mpr fun _ _ hc ho => ho.2 hc.2
  have cn : Disjoint C N := SimpleGraph.disjoint_left.mpr fun _ _ hc hn => hn.2 hc.1
  have on' : Disjoint O N := SimpleGraph.disjoint_left.mpr fun _ _ ho hn => hn.2 ho.1
  have cu : Disjoint C U := co.mono_right subU
  have cv : Disjoint C V := cn.mono_right subV
  have uv : Disjoint U V := on'.mono subU subV
  have comb : Disjoint (C ⊔ U) V := disjoint_sup_left.mpr ⟨cv,uv⟩
  have restore : C ⊔ O = F₀ := sup_inf_sdiff F₀ F₁
  refine ⟨sup_le (sup_le (inf_le_left.trans h₀) (subU.trans (sdiff_le.trans h₀)))
     (subV.trans (sdiff_le.trans h₁)),?_⟩
  intro v
  have old := neighbor_card_sup_of_disjoint co v
  rw [restore,oldDegree] at old
  have oldSplit := selectedGraph_degree O Set.univ srcO dstO orientO v
  simp only [selectedGraph_univ,Set.mem_univ,true_and] at oldSplit
  have red := selectedGraph_degree O A srcO dstO orientO v
  have blue := selectedGraph_degree N B srcN dstN orientN v
  have hs := sources v
  have hd := dests v
  change Nat.card (((C ⊔ U) ⊔ V).neighborSet v) = a + 2
  rw [neighbor_card_sup_of_disjoint comb,neighbor_card_sup_of_disjoint cu]
  change Nat.card (C.neighborSet v) + Nat.card ((selectedGraph O A).neighborSet v) +
    Nat.card ((selectedGraph N B).neighborSet v) = a + 2
  rw [red,blue]
  dsimp only [O,N] at old oldSplit hs hd ⊢
  omega

#print axioms factor_from_selection
end JSP452Audit.StarHost
