import WholeCoreShiftedRows
import ComponentSurplusSum
import PositiveCoreCaps
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Positive exposure forces a genuine ordinary component of order above D;
the whole core's matching rank is at least half D. -/
theorem ordinary_region_has_large_piece (G : SimpleGraph X) (D : ℕ) (pos : 0<D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (exposed : 0<minimumExposure G D)
    (K : DegreeRegion G D) :
    (∃c:(G.induce K.core).ConnectedComponent,D+1≤Nat.card c.supp) ∧
    D≤2*matchingEdges (G.induce K.core) := by
  classical
  let _ := Fintype.ofFinite ↥K.pieces
  have weight := K.weight_identity cap
  have dZ : (0:ℤ)<D := by exact_mod_cast pos
  have xZ : (0:ℤ)<minimumExposure G D := by exact_mod_cast exposed
  have product := mul_pos dZ xZ
  have positive : 0<edgeSurplus (G.induce K.core) D := by omega
  have sum := core_surplus_eq_sum G K.barrier K.pieces D
  change edgeSurplus (G.induce K.core) D=_ at sum
  have existsPos : ∃c:K.pieces,0<edgeSurplus ((G.induce K.barrierᶜ).induce c.val.supp) D := by
    by_contra! none
    have nonpos := Finset.sum_nonpos (s:=(Finset.univ : Finset ↥K.pieces)) (fun c _ => none c)
    rw [←sum] at nonpos
    omega
  obtain ⟨p,hp⟩ := existsPos
  let _ : Nonempty p.val.supp := p.val.nonempty_supp.to_subtype
  have bound (x:p.val.supp) : Nat.card (((G.induce K.barrierᶜ).induce p.val.supp).neighborSet x)≤D := by
    exact (induced_neighbor_count_le (G.induce K.barrierᶜ) p.val.supp x).trans
      ((induced_neighbor_count_le G K.barrierᶜ x.val).trans (cap _))
  have long := (positive_core_caps _ (K.critical p.val).2 D bound hp).1
  let e := coreComponentEquiv G K.barrier K.pieces
  let c := e.symm p
  have size := coreComponent_order G K.barrier K.pieces c
  change c.supp.ncard=(e c).val.supp.ncard at size
  rw [show e c=p from e.apply_symm_apply p] at size
  have big : D+1≤Nat.card c.supp := by rw [Nat.card_coe_set_eq,size,←Nat.card_coe_set_eq];exact long
  have order := factorCritical_order_rank c.toSimpleGraph (ordinary_core_components_critical G K c) c.nonempty_supp.to_subtype.some
  change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at order
  have small := rank_le_of_copy (SimpleGraph.Embedding.induce (G:=(G.induce K.core)) c.supp).toCopy
  change matchingEdges c.toSimpleGraph≤matchingEdges (G.induce K.core) at small
  exact ⟨⟨c,big⟩,by omega⟩

#print axioms ordinary_region_has_large_piece
end JSP452Audit.StarHost
