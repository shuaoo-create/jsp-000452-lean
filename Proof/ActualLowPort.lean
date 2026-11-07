import DegreeRegion
import GoodPortExchange

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A genuinely low internal port in a selected full original component has
an original incident edge from a root of this particular degree region. -/
theorem internal_low_adjacent_root {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (K : DegreeRegion G D) (c : (G.induce K.barrierᶜ).ConnectedComponent) (hc : c ∈ K.pieces)
    (y : c.supp) (low : Nat.card (c.toSimpleGraph.neighborSet y) < D) :
    ∃ r ∈ K.roots, G.Adj r y.val.val := by
  by_contra missing
  have external (z : G.neighborSet y.val.val) : z.val ∉ K.barrier := by
    intro root
    let a : K.barrier := ⟨z.val,root⟩
    have link : rootIncidence G K.barrier a c := ⟨y,z.property.symm⟩
    have actual : z.val ∈ K.roots := ⟨a,⟨c,hc,link⟩,rfl⟩
    exact missing ⟨z.val,actual,z.property.symm⟩
  let kept (z : G.neighborSet y.val.val) : ↥(K.barrierᶜ : Set X) := ⟨z.val,external z⟩
  have same (z : G.neighborSet y.val.val) : kept z ∈ c.supp :=
    c.mem_supp_of_adj_mem_supp y.property (show (G.induce K.barrierᶜ).Adj y.val (kept z) from z.property)
  let into (z : G.neighborSet y.val.val) : c.toSimpleGraph.neighborSet y :=
    ⟨⟨kept z,same z⟩,z.property⟩
  have inj : Function.Injective into := fun _ _ eq => Subtype.ext
    (congrArg (fun w : c.toSimpleGraph.neighborSet y => w.val.val.val) eq)
  have bound := Nat.card_le_card_of_injective into inj
  have full : Nat.card (G.neighborSet y.val.val) = D := K.full hc y
  omega

/-- Negating the good-port test exhibits the original labels and an actual
near-perfect matching failing that test. -/
theorem not_good_port_witness {Y : Type*} (Q : SimpleGraph Y) (y : Y) (bad : ¬GoodPort Q y) :
    ∃ v : Y, v ≠ y ∧ ∃ M : Q.Subgraph, M.IsMatching ∧ M.verts = {x | x ≠ v} ∧
      ∃ z : Y, M.Adj y z ∧ ¬ Q.Adj v z := by
  classical
  unfold GoodPort at bad
  push Not at bad
  exact bad

#print axioms internal_low_adjacent_root
#print axioms not_good_port_witness
end JSP452Audit.StarHost
