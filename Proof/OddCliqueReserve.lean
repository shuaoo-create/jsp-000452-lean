import CliqueDissociation
import EnvelopeFirstGain
import EnvelopeDisjointUnion
namespace JSP452Audit.StarHost
open SimpleGraph
/-- The first envelope layer saves at least one edge on every odd clique
of order at least five. The certificate holds at every nonzero truncation. -/
theorem odd_clique_reserve (z : ℕ) (hz : 2≤z) (k : ℕ) :
    1 ≤ envelopeReserve (⊤ : SimpleGraph (Fin (2*z+1))) (k+1) := by
  let C : SimpleGraph (Fin (2*z+1)) := ⊤
  change 1 ≤ envelopeReserve C (k+1)
  have gain := envelope_first_gain C k
  have bound := envelope_two_vertex_bound C
  rw [Nat.card_fin] at bound
  have exactCost := clique_deletion_one z hz
  change deletionBudget C 1=2*z-1 at exactCost
  omega

theorem odd_clique_summand_gain {X : Type*} [Finite X] (G : SimpleGraph X) (z : ℕ) (hz : 2≤z) (k : ℕ) :
    envelopeReserve G (k+1)+1 ≤ envelopeReserve (G ⊕g (⊤ : SimpleGraph (Fin (2*z+1)))) (k+1) := by
  have gain := odd_clique_reserve z hz k
  have pay := envelopeReserve_superadditive G (⊤ : SimpleGraph (Fin (2*z+1))) (k+1)
  omega
#print axioms odd_clique_reserve
#print axioms odd_clique_summand_gain
end JSP452Audit.StarHost