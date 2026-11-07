import GapTwoFourRealPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

noncomputable def jointPhysicalInventory {D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (j : ℕ) : ℕ :=
  K.roots.ncard+2*matchingEdges (G.induce K.core)+uniformEnvelope (G.induce K.rest) j+
    uniformEnvelope (eraseInternal G K.core) j

theorem joint_physical_sum {D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D) :
    (∑z∈Finset.range (D-1),jointPhysicalInventory G K (z+2))=
    (D-1)*(K.roots.ncard+2*matchingEdges (G.induce K.core))+interiorInventory (G.induce K.rest) D+
      interiorInventory (eraseInternal G K.core) D := by
  unfold jointPhysicalInventory interiorInventory
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib];simp

theorem physical_dominates_basic {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (ht : 0<t) (esc : matchingEdges (G.induce K.core)<s) (d : ℕ)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r)) (j : ℕ) (pos : 0<j) :
    basicCapacity G K n m r j≤jointPhysicalInventory G K j := by
  let H := G.induce K.core
  let μ := matchingEdges H
  let a := K.roots.ncard
  let W := componentBudget H n
  let J := commonErasedDemand n W a μ
  obtain ⟨_,fit,row,_,_,_,_,_⟩ := data.1
  change W.loss≤μ at fit;change μ<s at esc
  have len : 0<W.len := by dsimp only [RemovalBudget.len];omega
  have b := widthAt_le_uniformEnvelope len ht (W.entries n) m (W.entries_antitone n hn) hm (W.entries_positive n pn)
    pm _ (r+a) j row pos
  have z := widthAt_le_uniformEnvelope len ht J m (common_erased_antitone n hn W a μ) hm
    (common_erased_positive n W a μ) pm _ r j data.2.1 pos
  exact Nat.add_le_add (Nat.add_le_add_left b _) z

theorem even_cut_both_envelopes {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (ht : 0<t) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (fits : t+∑j,(m j-1)/2≤matchingEdges (G.induce K.core)) (j : ℕ) (pos : 0<j) :
    let μ := matchingEdges (G.induce K.core)
    let q := μ+1-t
    let f := originalThresholdCount n j
    f≤uniformEnvelope (G.induce K.rest) j+2*q+r+K.roots.ncard ∧
    f≤uniformEnvelope (eraseInternal G K.core) j+2*q+r := by
  intro μ q f
  let Y := ∑j,(m j-1)/2
  let w := μ+1-(t+Y)
  let V := halfOrderBudget m (μ-w)
  obtain ⟨v,actual⟩ := exact_axis_repair_inventory G K n m hn hm pn pm ht row fits
  change 0<V.len at v
  have repair := actual j pos
  change 2*w<f → f-2*w+V.len-1-(r+K.roots.ncard)≤uniformEnvelope (G.induce K.rest) j ∧
    f-2*w+V.len-1-r≤uniformEnvelope (eraseInternal G K.core) j at repair
  have small : w≤q := by dsimp [w,q];omega
  by_cases many : 2*w<f
  · obtain ⟨b,z⟩ := repair many;omega
  · omega

#print axioms joint_physical_sum
#print axioms physical_dominates_basic
#print axioms even_cut_both_envelopes
end JSP452Audit.StarHost