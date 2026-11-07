import InsideClique
import MixedPortCounts
import MixedPortUncovered
import PortFullSize
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
/-- The full-degree vertices form a clique in the mixed case, for every
number of low vertices and every finite type of original vertex labels. -/
theorem full_set_of_mixed_ports_is_clique (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ x∈portLow Q D,GoodPort Q x) (v : X) (hv : v∈portFull Q D)
    (lows : (portLow Q D).Nonempty) : Q.IsClique (portFull Q D) := by
  have dense : Q.induce (portFull Q D) = ⊤ := by
    by_cases small : (portLow Q D).ncard ≤ 2
    · exact portFull_complete_few_low Q D cap crit good ((Set.ncard_pos (portLow Q D).toFinite).mpr lows) small
    obtain ⟨m,shape⟩ := good_port_split_arithmetic Q D cap crit good v hv
    have count : Nat.card ↥(portFull Q D)=2*m+(portLow Q D).ncard+1 :=
      (Nat.card_coe_set_eq _).trans shape
    apply complete_of_unmatched_cliques _ m (portLow Q D).ncard count (by omega)
      (portFull_matching_floor Q D m cap crit v shape)
    intro M hm card
    have verts := Set.ncard_add_ncard_compl M.verts
    rw [matching_vertices_eq_twice_edges hm,card,count] at verts
    exact uncovered_clique_of_good_low Q D cap crit good M hm (by omega)
  intro x hx y hy diff
  change (Q.induce (portFull Q D)).Adj ⟨x,hx⟩ ⟨y,hy⟩
  rw [dense]
  exact fun eq => diff (congrArg Subtype.val eq)
#print axioms full_set_of_mixed_ports_is_clique
end JSP452Audit.StarHost
