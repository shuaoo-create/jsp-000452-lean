import RegionDegreeSum
import PartitionHandshake
namespace JSP452Audit.StarHost
open SimpleGraph
noncomputable def rootShortfall {X : Type*} [Finite X] (G : SimpleGraph X) (A : Set X) (D : ℕ) : ℕ :=
  D*A.ncard - originalDegreeSum G A

/-- Original edge identity on any three actual regions satisfying the
rank/order and degree hypotheses, without dropping a negative component. -/
theorem weight_handshake {X : Type*} [Finite X] (G : SimpleGraph X) (A C B : Set X)
    (D rho : ℕ) (cap : ∀ x∈A, Nat.card (G.neighborSet x)≤D)
    (full : ∀ x∈C, Nat.card (G.neighborSet x)=D)
    (ac : Disjoint A C) (ab : Disjoint A B) (cb : Disjoint C B)
    (cover : A∪C∪B=Set.univ) (sep : ∀ x∈C, ∀ y∈B, ¬G.Adj x y)
    (order : C.ncard=2*matchingEdges (G.induce C)+A.ncard+rho) :
    2*edgeSurplus (G.induce C) D =
      (D:ℤ)*rho + (rootShortfall G A D:ℤ) + 2*((G.induce A).edgeSet.ncard:ℤ)+(crossCount G A B:ℤ) := by
  have root := partition_handshake G A C B ac ab cb cover
  have core := partition_handshake G C A B ac.symm cb ab (by rwa [Set.union_comm C A])
  rw [degree_sum_full G C D full,crossCount_of_no_edges G C B sep,Nat.add_zero,crossCount_swap G C A] at core
  have sd : rootShortfall G A D + originalDegreeSum G A = D*A.ncard :=
    Nat.sub_add_cancel (degree_sum_le_cap G A D cap)
  rw [order] at core
  simp only [Nat.mul_add] at core
  have rootZ := congrArg (fun k : ℕ => (k:ℤ)) root
  have coreZ := congrArg (fun k : ℕ => (k:ℤ)) core
  have sdZ := congrArg (fun k : ℕ => (k:ℤ)) sd
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at rootZ coreZ sdZ
  unfold edgeSurplus
  rw [mul_left_comm (D:ℤ) 2] at coreZ
  omega

#print axioms weight_handshake
end JSP452Audit.StarHost