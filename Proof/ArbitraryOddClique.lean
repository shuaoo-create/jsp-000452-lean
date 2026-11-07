import OddCliqueReserve
import ComponentZeroReserve
import HostIsoRow

namespace JSP452Audit.StarHost
open SimpleGraph

private theorem uniformEnvelope_le_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H) (h : ℕ) :
    uniformEnvelope G h ≤ uniformEnvelope H h := by
  by_cases pos : 0 < uniformEnvelope G h
  · obtain ⟨a,b,p,q,ha,hb,hp,hq,height,width,force⟩ := uniformEnvelope_attained G h pos
    rw [← width]
    exact uniform_pair_le_envelope H a b p q h ha hb hp hq height (forces_of_iso e force)
  · omega

theorem uniformEnvelope_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H) (h : ℕ) :
    uniformEnvelope G h = uniformEnvelope H h :=
  le_antisymm (uniformEnvelope_le_iso e h) (uniformEnvelope_le_iso e.symm h)

theorem envelopeReserve_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H) (h : ℕ) :
    envelopeReserve G h = envelopeReserve H h := by
  have edges : G.edgeSet.ncard = H.edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  have layers : uniformEnvelope G = uniformEnvelope H := funext (uniformEnvelope_iso e)
  simp only [envelopeReserve,edges,rank_eq_of_graph_iso e,layers]

/-- The odd-clique reserve applies to any finite label type of the indicated order. -/
theorem odd_clique_reserve_of_order {X : Type*} [Finite X] (z k : ℕ)
    (order : Nat.card X=2*z+1) (hz : 2≤z) :
    1≤envelopeReserve (⊤ : SimpleGraph X) (k+1) := by
  classical
  let _ := Fintype.ofFinite X
  let labels : X ≃ Fin (2*z+1) := Fintype.equivOfCardEq (by
    rwa [Fintype.card_fin,← Nat.card_eq_fintype_card])
  let iso : (⊤ : SimpleGraph X) ≃g (⊤ : SimpleGraph (Fin (2*z+1))) := {
    toEquiv := labels
    map_rel_iff' := labels.injective.ne_iff }
  rw [envelopeReserve_iso iso]
  exact odd_clique_reserve z hz k

#print axioms envelopeReserve_iso
#print axioms odd_clique_reserve_of_order
end JSP452Audit.StarHost
