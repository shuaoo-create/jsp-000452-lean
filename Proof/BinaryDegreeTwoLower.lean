import BinaryHostAccounting
import FlexibleComponents
import ThinDegreeTwoCut
import BinaryCoverValues
import OrdinaryBinaryReduction
import PruneIsolates
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Contradiction for a strict degree-two host with no isolated vertices.
The flexible and low-order colorings are both true colorings of the given graph. -/
theorem ordinary_binary_no_isolate_lower {X : Type u} [Finite X] (G : SimpleGraph X)
    (p q a b : ℕ) (hp : 0<p) (hq : 0<q)
    (cap : ∀ v, Nat.card (G.neighborSet v) ≤ 2)
    (noIso : ∀ v, 0 < Nat.card (G.neighborSet v))
    (force : Forces G (forest (binaryProfile p a)) (forest (binaryProfile q b))) :
    3*(p+q-1)+2*max a b+min a b ≤ G.edgeSet.ncard := by
  by_contra! under
  obtain ⟨edges,rank,_,two,_⟩ := strict_binary_tight G p q a b hp hq force
    (canSplitRank_of_degree_le_two G cap) under
  have units := degree_two_edges_le_rank_budget G cap
  have mpos : 1 ≤ min a b := by omega
  by_cases ample : 2 ≤ pathCapacity G
  · have exactSplit := exactRankSplit_of_flexible G (exactRankSplit_of_pathLike G cap)
      (binary_strict_component_rank_cap G p q a b hp hq force cap under) ample
    have lower := exact_split_forcing_floor G (show 0<p+a by omega) (show 0<q+b by omega)
      (binaryProfile p a) (binaryProfile q b) (binaryProfile_positive p a) (binaryProfile_positive q b)
      force exactSplit
    omega
  · have size := degree_two_order_le_edges_pathCapacity G cap noIso
    let _ : Nonempty (Fin (p+a)) := ⟨⟨0,by omega⟩⟩
    let _ : Nonempty (Fin (q+b)) := ⟨⟨0,by omega⟩⟩
    have price := forced_forest_order_le_edges_add_four G cap (binaryProfile p a) (binaryProfile q b)
      (binaryProfile_positive p a) (binaryProfile_positive q b) force (by omega)
    rw [binary_vertices,binary_vertices] at price
    omega

theorem ordinary_binary_degree_two_lower {X : Type u} [Finite X] (G : SimpleGraph X)
    (p q a b : ℕ) (hp : 0<p) (hq : 0<q) (cap : ∀v,Nat.card (G.neighborSet v)≤2)
    (force : Forces G (forest (binaryProfile p a)) (forest (binaryProfile q b))) :
    3*(p+q-1)+2*max a b+min a b ≤ G.edgeSet.ncard := by
  obtain ⟨eq,degs,keep⟩ := isolate_free_support_host G 2 (binaryProfile p a) (binaryProfile q b)
    (binaryProfile_positive p a) (binaryProfile_positive q b) cap force
  exact (ordinary_binary_no_isolate_lower (G.induce G.support) p q a b hp hq (fun x => (degs x).2)
    (fun x => (degs x).1) keep).trans_eq eq
#print axioms ordinary_binary_degree_two_lower
#print axioms ordinary_binary_no_isolate_lower
end JSP452Audit.StarHost