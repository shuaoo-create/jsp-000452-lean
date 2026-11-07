import GoodPortExchange
import FactorCriticalPeak

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X]

def portFull (Q : SimpleGraph X) (D : ℕ) : Set X := {v | Nat.card (Q.neighborSet v) = D}
def portLow (Q : SimpleGraph X) (D : ℕ) : Set X := {v | Nat.card (Q.neighborSet v) < D}

private theorem expose_any (Q : SimpleGraph X) (crit : PerfectAfterEveryDeletion Q) (v : X) :
    ∃ M : Q.Subgraph, M.IsMatching ∧ M.verts = {w | w ≠ v} := by
  obtain ⟨P,h⟩ := crit v
  obtain ⟨M,hm,verts,_⟩ := lift_perfect_off_vertex_maximum Q v P h
  exact ⟨M,hm,verts⟩

/-- When all vertices are good, expose x and let z be the partner of y.
Goodness of z forces the edge from x to y. -/
theorem all_good_ports_complete (Q : SimpleGraph X) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ x, GoodPort Q x) : Q = ⊤ := by
  apply top_unique
  intro x y xy
  have diff : x ≠ y := xy
  obtain ⟨M,hm,verts⟩ := expose_any Q crit x
  obtain ⟨z,yz,_⟩ := hm (show y∈M.verts by rw [verts]; exact diff.symm)
  have zUsed := M.edge_vert yz.symm
  rw [verts] at zUsed
  exact good z x (Ne.symm zUsed) M hm verts y yz.symm

theorem all_low_ports_complete (Q : SimpleGraph X) (D : ℕ) (crit : PerfectAfterEveryDeletion Q)
    (allLow : ∀ x, x ∈ portLow Q D) (good : ∀ x ∈ portLow Q D, GoodPort Q x) : Q = ⊤ :=
  all_good_ports_complete Q crit (fun x => good x (allLow x))

/-- A matched good vertex y with a full exposed vertex v forces both v--y and
the full degree of its actual partner z by the good-port degree inequality. -/
theorem good_mate_of_full_exposure (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) {v y z : X} (full : v∈portFull Q D)
    (good : GoodPort Q y) (M : Q.Subgraph) (hm : M.IsMatching)
    (verts : M.verts = {x | x ≠ v}) (yz : M.Adj y z) : Q.Adj v y ∧ z∈portFull Q D := by
  classical
  have bound := good_port_degree_bound Q good M hm verts yz
  have capZ := cap z
  change Nat.card (Q.neighborSet v) = D at full
  change Q.Adj v y ∧ Nat.card (Q.neighborSet z) = D
  rw [full] at bound
  by_cases adjacent : Q.Adj v y
  · simp only [if_pos adjacent] at bound
    exact ⟨adjacent,by omega⟩
  · simp only [if_neg adjacent] at bound
    omega

/-- Every full vertex is adjacent to every low good vertex. -/
theorem full_adj_good_low (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ y ∈ portLow Q D, GoodPort Q y) {v y : X} (full : v∈portFull Q D)
    (low : y∈portLow Q D) : Q.Adj v y := by
  have diff : y ≠ v := by
    intro eq; subst y
    exact Nat.ne_of_lt low full
  obtain ⟨M,hm,verts⟩ := expose_any Q crit v
  obtain ⟨z,yz,_⟩ := hm (show y∈M.verts by rw [verts]; exact diff)
  exact (good_mate_of_full_exposure Q D cap full (good y low) M hm verts yz).1

/-- For each matching exposing v, use its own partner edge to inject all low
vertices into the remaining full vertices, with all original labels intact. -/
theorem good_low_mates_full (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (good : ∀ y ∈ portLow Q D, GoodPort Q y)
    (v : X) (full : v∈portFull Q D) (M : Q.Subgraph) (hm : M.IsMatching)
    (verts : M.verts = {x | x ≠ v}) :
    ∃ f : ↥(portLow Q D) ↪ ↥(portFull Q D \ {v}), ∀ y, M.Adj y.val (f y).val := by
  classical
  have mate (y : portLow Q D) : ∃ z : ↥(portFull Q D \ {v}), M.Adj y.val z.val := by
    have diff : y.val ≠ v := by
      intro eq
      exact Nat.ne_of_lt y.property (eq ▸ full)
    obtain ⟨z,yz,_⟩ := hm (show y.val∈M.verts by rw [verts]; exact diff)
    have fullZ := (good_mate_of_full_exposure Q D cap full (good y.val y.property) M hm verts yz).2
    have used := M.edge_vert yz.symm
    rw [verts] at used
    exact ⟨⟨z,fullZ,fun eq => used (Set.mem_singleton_iff.mp eq)⟩,yz⟩
  choose f adj using mate
  have inj : Function.Injective f := by
    intro y w eq
    exact Subtype.ext (hm.eq_of_adj_right (adj y) (eq ▸ adj w))
  exact ⟨⟨f,inj⟩,adj⟩

theorem low_add_one_le_full (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ y ∈ portLow Q D, GoodPort Q y) (v : X) (full : v∈portFull Q D) :
    (portLow Q D).ncard+1 ≤ (portFull Q D).ncard := by
  obtain ⟨M,hm,verts⟩ := expose_any Q crit v
  obtain ⟨f,_⟩ := good_low_mates_full Q D cap good v full M hm verts
  have injects := Nat.card_le_card_of_injective f f.injective
  change (portLow Q D).ncard ≤ (portFull Q D \ {v}).ncard at injects
  have all := Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr full)
  rw [Set.ncard_singleton] at all
  omega

#print axioms all_good_ports_complete
#print axioms full_adj_good_low
#print axioms good_low_mates_full
#print axioms low_add_one_le_full
end JSP452Audit.StarHost
