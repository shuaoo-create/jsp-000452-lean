import ExactDeficiency
import FactorDualCut
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace JSP452Audit.Padded
open SimpleGraph

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

private noncomputable abbrev valence (C : SimpleGraph V) (x : V) := (C.neighborSet x).ncard
private noncomputable abbrev defect (C : SimpleGraph V) (x : V) :=
  (valence C x - P.A x) + (P.G.degree x - valence C x - P.B x)

private theorem shave_side (F : SimpleGraph V) {u v : V} (edge : F.Adj u v) :
    valence (F.deleteEdges {s(u,v)}) u + 1 = valence F u := by
  have nbr : (F.deleteEdges {s(u,v)}).neighborSet u = F.neighborSet u \ {v} := by
    ext x
    simp [SimpleGraph.mem_neighborSet,SimpleGraph.deleteEdges_adj,edge.ne]
  rw [valence,nbr]
  exact Set.ncard_sdiff_singleton_add_one edge

omit [Fintype V] in
private theorem shave_other (F : SimpleGraph V) {u v x : V} (xu : x ≠ u) (xv : x ≠ v) :
    valence (F.deleteEdges {s(u,v)}) x = valence F x := by
  have nbr : (F.deleteEdges {s(u,v)}).neighborSet x = F.neighborSet x := by
    ext w
    simp [SimpleGraph.mem_neighborSet,SimpleGraph.deleteEdges_adj,xu,xv]
  rw [valence,nbr]

private theorem shaved_gap (F : SimpleGraph V) {u v : V} (edge : F.Adj u v)
    (over : P.A u < valence F u) (caps : ∀ x, P.G.degree x ≤ P.A x + P.B x) :
    P.colorGap (F.deleteEdges {s(u,v)}) ≤ P.colorGap F := by
  classical
  let H := F.deleteEdges {s(u,v)}
  have du : valence H u + 1 = valence F u := shave_side F edge
  have dv : valence H v + 1 = valence F v := by
    simpa only [H,Sym2.eq_swap (a := v) (b := u)] using shave_side F edge.symm
  have balance (x : V) :
      defect P H x + (if x = u then 1 else 0) ≤ defect P F x + (if x = v then 1 else 0) := by
    by_cases hx : x = u
    · subst x
      simp [edge.ne]
      have cap := caps u
      dsimp only [defect]
      omega
    by_cases hv : x = v
    · subst x
      simp [hx]
      dsimp only [defect]
      omega
    · simp only [if_neg hx,if_neg hv,Nat.add_zero]
      have other : valence H x = valence F x := shave_other F hx hv
      simp only [defect,other,le_refl]
  have total := Finset.sum_le_sum (s := Finset.univ) (fun x _ => balance x)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] at total
  change (∑ x, defect P H x) ≤ (∑ x, defect P F x)
  simp only [defect, Finset.sum_add_distrib]
  omega

/-- Remove actual original edges only; the loss of one unit of red excess
at an overloaded endpoint pays for any new blue excess at the other endpoint. -/
theorem Spec.cap_red_without_gap_increase (caps : ∀ x, P.G.degree x ≤ P.A x + P.B x)
    (F : SimpleGraph V) : ∃ H ≤ F, (∀ x, Nat.card (H.neighborSet x) ≤ P.A x) ∧ P.colorGap H ≤ P.colorGap F := by
  classical
  induction F using WellFounded.induction (measure (fun H : SimpleGraph V => H.edgeSet.ncard)).wf with
  | h F ih =>
    by_cases done : ∀ x, valence F x ≤ P.A x
    · exact ⟨F,le_rfl,done,le_rfl⟩
    push Not at done
    obtain ⟨u,over⟩ := done
    have pos : 0 < (F.neighborSet u).ncard := Nat.zero_lt_of_lt over
    obtain ⟨v,edge⟩ := (Set.ncard_pos (s := F.neighborSet u)).mp pos
    let H := F.deleteEdges {s(u,v)}
    have fewer : H.edgeSet.ncard < F.edgeSet.ncard := by
      have adj : s(u,v) ∈ F.edgeSet := F.mem_edgeSet.mpr edge
      have diff := Set.ncard_sdiff_singleton_add_one adj
      rw [show H.edgeSet = F.edgeSet \ {s(u,v)} from F.edgeSet_deleteEdges _]
      omega
    obtain ⟨J,leH,bound,gap⟩ := ih H fewer
    exact ⟨J,leH.trans (F.deleteEdges_le _),bound,gap.trans (shaved_gap P F edge over caps)⟩

/-- A single optimal red graph obeys the red caps; all its deficiency is actual
blue excess in the complement in the original host. -/
theorem Spec.capped_optimal (caps : ∀ x, P.G.degree x ≤ P.A x + P.B x) :
    ∃ H ≤ P.G, (∀ x, Nat.card (H.neighborSet x) ≤ P.A x) ∧
      (∑ x, (Nat.card ((P.G \ H).neighborSet x) - P.B x)) = P.minColorGap := by
  classical
  let vals : Set ℕ := {n | ∃ F : SimpleGraph V, F ≤ P.G ∧ P.colorGap F = n}
  have attained : sInf vals ∈ vals := Nat.sInf_mem ⟨_,⊥,bot_le,rfl⟩
  obtain ⟨F,leG,best⟩ := attained
  obtain ⟨H,sub,ok,improved⟩ := P.cap_red_without_gap_increase caps F
  have incl := sub.trans leG
  have lower : P.minColorGap ≤ P.colorGap H := Nat.sInf_le (s := vals) ⟨H,incl,rfl⟩
  have eq : P.colorGap H = P.minColorGap := le_antisymm (improved.trans_eq best) lower
  refine ⟨H,incl,ok,?_⟩
  rw [← eq]
  apply Finset.sum_congr rfl
  intro x _
  have nei : H.neighborSet x ⊆ P.G.neighborSet x := fun _ h => incl h
  have host : (P.G.neighborSet x).ncard = P.G.degree x := by
    rw [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]
  rw [Nat.card_coe_set_eq,SimpleGraph.neighborSet_sdiff,Set.ncard_sdiff nei,host]
  change _ = (valence H x - P.A x) + (P.G.degree x - valence H x - P.B x)
  have capH : valence H x ≤ P.A x := ok x
  rw [Nat.sub_eq_zero_of_le capH,zero_add]

/-- A common bound proved for every cut gives one actual capped coloring. -/
theorem Spec.capped_color_of_cut_bounds (caps : ∀ x, P.G.degree x ≤ P.A x + P.B x)
    (b : Bool) (K : ℕ)
    (cuts : ∀ S T : Set V, Disjoint S T →
      JSP452Audit.StarHost.retainedScore (P.withPoolBit b).graph ((P.withPoolBit b).canonicalKept S T) ≤
        Nat.card (P.withPoolBit b).Vertex + K) :
    ∃ H ≤ P.G, (∀ x, Nat.card (H.neighborSet x) ≤ P.A x) ∧
      (∑ x, (Nat.card ((P.G \ H).neighborSet x) - P.B x)) ≤ K := by
  obtain ⟨H,leG,capped,eq⟩ := P.capped_optimal caps
  exact ⟨H,leG,capped,eq.le.trans (P.color_gap_of_cut_bounds caps b K cuts)⟩

/-- Clear the common denominator in any rational cut bound. The same actual
coloring satisfies the bound; no single flow atom need control every cut. -/
theorem Spec.capped_color_of_scaled_cuts (caps : ∀ x, P.G.degree x ≤ P.A x + P.B x)
    {den num : ℕ} (pos : 0 < den)
    (cuts : ∀ S T : Set V, Disjoint S T → (den : ℤ) * P.cutDeficit S T ≤ (num : ℤ)) :
    ∃ H ≤ P.G, (∀ x, Nat.card (H.neighborSet x) ≤ P.A x) ∧
      (∑ x, (Nat.card ((P.G \ H).neighborSet x) - P.B x)) ≤ num / den := by
  obtain ⟨S,T,dis,attains⟩ := (P.exact_factor_deficiency caps).2
  have bound := cuts S T dis
  rw [attains, ← Int.natCast_mul] at bound
  have scaled : den * P.minColorGap ≤ num := by exact_mod_cast bound
  obtain ⟨H,hh,capped,loss⟩ := P.capped_optimal caps
  refine ⟨H,hh,capped,?_⟩
  rw [loss,Nat.le_div_iff_mul_le pos,Nat.mul_comm]
  exact scaled

#print axioms Spec.capped_color_of_scaled_cuts
#print axioms Spec.capped_color_of_cut_bounds
#print axioms Spec.cap_red_without_gap_increase
#print axioms Spec.capped_optimal
end JSP452Audit.Padded
