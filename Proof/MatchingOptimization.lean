import UnmatchedTotal
import ChooseParity
import RealizeGivenEven
import ActualPoolParity

namespace JSP452Audit.Padded
variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

noncomputable def Spec.colorGap (F : SimpleGraph V) : ℕ :=
  ∑ v, ((Nat.card (F.neighborSet v) - P.A v) +
    (P.G.degree v - Nat.card (F.neighborSet v) - P.B v))

/-- Optimize over actual original red subgraphs and actual auxiliary matchings. -/
noncomputable def Spec.minColorGap : ℕ :=
  sInf {n : ℕ | ∃ F : SimpleGraph V, F ≤ P.G ∧ P.colorGap F = n}

noncomputable def minUnmatched {W : Type*} [Finite W] (G : SimpleGraph W) : ℕ :=
  sInf {n : ℕ | ∃ M : G.Subgraph, M.IsMatching ∧ Nat.card {x : W // x ∉ M.verts} = n}

private theorem minUnmatched_attained {W : Type*} [Finite W] (G : SimpleGraph W) :
    ∃ M : G.Subgraph, M.IsMatching ∧ Nat.card {x : W // x ∉ M.verts} = minUnmatched G := by
  apply Nat.sInf_mem (s := {n : ℕ | ∃ M : G.Subgraph, M.IsMatching ∧ Nat.card {x : W // x ∉ M.verts} = n})
  exact ⟨_, ⊥,(by intro x hx; exact False.elim hx),rfl⟩

private theorem minColor_attained :
    ∃ F : SimpleGraph V, F ≤ P.G ∧ P.colorGap F = P.minColorGap := by
  apply Nat.sInf_mem (s := {n : ℕ | ∃ F : SimpleGraph V, F ≤ P.G ∧ P.colorGap F = n})
  exact ⟨_, ⊥,bot_le,rfl⟩

theorem Spec.minColorGap_le_graphGap (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    P.minColorGap ≤ minUnmatched P.graph := by
  obtain ⟨M,matchM,eq⟩ := minUnmatched_attained P.graph
  have lower : P.minColorGap ≤ P.colorGap (P.redShadow M) :=
    Nat.sInf_le (show _ ∈ {n : ℕ | ∃ F : SimpleGraph V, F ≤ P.G ∧ P.colorGap F = n} from
      ⟨P.redShadow M,P.redShadow_le M,rfl⟩)
  exact lower.trans ((P.shadowDeviation_le_unmatched M matchM caps).trans_eq eq)

private theorem equality_of_realization (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v)
    (reach : ∀ F : SimpleGraph V, F ≤ P.G →
      ∃ b : Bool, ∃ M : (P.withPoolBit b).graph.Subgraph, M.IsMatching ∧
        Nat.card {x : (P.withPoolBit b).Vertex // x ∉ M.verts} = P.colorGap F) :
    P.minColorGap = min (minUnmatched (P.withPoolBit false).graph)
      (minUnmatched (P.withPoolBit true).graph) := by
  apply Nat.le_antisymm
  · exact le_min ((P.withPoolBit false).minColorGap_le_graphGap caps)
      ((P.withPoolBit true).minColorGap_le_graphGap caps)
  obtain ⟨F,hF,best⟩ := minColor_attained P
  obtain ⟨b,M,hM,card⟩ := reach F hF
  have h : minUnmatched (P.withPoolBit b).graph ≤ P.colorGap F :=
    Nat.sInf_le (show _ ∈ {n : ℕ | ∃ N : (P.withPoolBit b).graph.Subgraph,
      N.IsMatching ∧ Nat.card {x : (P.withPoolBit b).Vertex // x ∉ N.verts} = n} from ⟨M,hM,card⟩)
  rw [← best]
  cases b with
  | false => exact (min_le_left _ _).trans h
  | true => exact (min_le_right _ _).trans h

#print axioms Spec.minColorGap_le_graphGap
/-- Every original coloring is realized with its exact deficit for one of the two
    auxiliary parity choices; the matching projects to precisely the original coloring. -/
theorem Spec.realizeColorGap (F : SimpleGraph V) (hF : F ≤ P.G)
    (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    ∃ b : Bool, ∃ M : (P.withPoolBit b).graph.Subgraph, M.IsMatching ∧
      (P.withPoolBit b).redShadow M = F ∧
      Nat.card {x : (P.withPoolBit b).Vertex // x ∉ M.verts} = P.colorGap F := by
  obtain ⟨b,even⟩ := P.exists_even_freePool_cross_local F
  obtain ⟨M,hM,hS,hc⟩ := (P.withPoolBit b).realize_given_even F hF caps even
  exact ⟨b,M,hM,hS,hc⟩

/-- Exact optimization identity over the two *actual* finite auxiliary graphs. -/
theorem Spec.minColorGap_eq_matching (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    P.minColorGap = min (minUnmatched (P.withPoolBit false).graph)
      (minUnmatched (P.withPoolBit true).graph) := by
  apply equality_of_realization P caps
  intro F hF
  obtain ⟨b,M,hM,_,hc⟩ := P.realizeColorGap F hF caps
  exact ⟨b,M,hM,hc⟩

#print axioms Spec.realizeColorGap
#print axioms Spec.minColorGap_eq_matching

end JSP452Audit.Padded
