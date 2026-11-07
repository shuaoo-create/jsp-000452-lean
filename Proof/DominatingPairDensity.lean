import DominatingPairReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Count the distinct possible ends of two-step walks from x. For each
first neighbor z, its return edge to x has to be excluded. -/
theorem common_neighbors_force_order_bound (H : SimpleGraph X) (r : ℕ)
    (reg : ∀x,Nat.card (H.neighborSet x)=r) (x : X)
    (common : ∀y,y≠x → ∃z,H.Adj x z ∧ H.Adj y z) :
    Nat.card X-1 ≤ r*(r-1) := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  let next (z : X) := (H.neighborFinset z).erase x
  have sub : Finset.univ.erase x ⊆ (H.neighborFinset x).biUnion next := by
    intro y hy
    obtain ⟨z,xz,yz⟩ := common y (Finset.mem_erase.mp hy).1
    exact Finset.mem_biUnion.mpr ⟨z,(H.mem_neighborFinset x z).mpr xz,
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1,(H.mem_neighborFinset z y).mpr yz.symm⟩⟩
  have cardN (z : X) : (H.neighborFinset z).card=r := by
    rw [H.card_neighborFinset_eq_degree,←H.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
    exact reg z
  have count : ∀z∈H.neighborFinset x,(next z).card=r-1 := by
    intro z hz
    exact (Finset.card_erase_of_mem ((H.mem_neighborFinset z x).mpr
      ((H.mem_neighborFinset x z).mp hz).symm)).trans (congrArg (fun a : ℕ => a-1) (cardN z))
  have room := (Finset.card_le_card sub).trans Finset.card_biUnion_le
  rw [Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,←Nat.card_eq_fintype_card,
    Finset.sum_congr rfl count] at room
  simpa [cardN] using room

/-- For any prescribed x in a regular host the numerical condition produces
an actual other vertex y dominating with x. No classification is assumed. -/
theorem exists_dominating_partner_of_density (Q : SimpleGraph X) (D : ℕ)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (x : X)
    (dense : let r:=Nat.card X-1-D; r*(r-1)<Nat.card X-1) :
    ∃ y,x≠y ∧ ∀v,v≠x → v≠y → Q.Adj v x ∨ Q.Adj v y := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  let r := Nat.card X-1-D
  have creg (z : X) : Nat.card (Qᶜ.neighborSet z)=r := by
    change Nat.card (Qᶜ.neighborSet z)=Nat.card X-1-D
    have deg : Q.degree z=D := by
      rw [←Q.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
      exact reg z
    rw [Nat.card_eq_fintype_card,Qᶜ.card_neighborSet_eq_degree,Q.degree_compl,
      deg,Nat.card_eq_fintype_card]
  by_contra! bad
  have two (y : X) (hy : y≠x) : ∃ z,Qᶜ.Adj x z ∧ Qᶜ.Adj y z := by
    obtain ⟨z,zx,zy,nx,ny⟩ := bad y hy.symm
    exact ⟨z,(Q.compl_adj _ _).mpr ⟨zx.symm,fun h => nx h.symm⟩,
      (Q.compl_adj _ _).mpr ⟨zy.symm,fun h => ny h.symm⟩⟩
  exact (Nat.not_lt_of_ge (common_neighbors_force_order_bound Qᶜ r creg x two)) dense

/-- The established two-point deletion budget now covers this numerical
class of regular critical components at every truncation height. -/
theorem dense_regular_component_pays [Nonempty X] (Q : SimpleGraph X) (D k : ℕ) (four : 4≤D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (dense : let r:=Nat.card X-1-D; r*(r-1)<Nat.card X-1) :
    minimumExposure Q D≤envelopeReserve Q k := by
  let x := Classical.choice ‹Nonempty X›
  obtain ⟨y,ne,dom⟩ := exists_dominating_partner_of_density Q D reg x dense
  exact regular_dominating_pair_pays Q D k four reg crit x y ne dom

#print axioms common_neighbors_force_order_bound
#print axioms exists_dominating_partner_of_density
#print axioms dense_regular_component_pays
end JSP452Audit.StarHost
