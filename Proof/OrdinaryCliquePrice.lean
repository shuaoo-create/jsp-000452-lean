import ActiveBoundaryPrice
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Every nontrivial odd clique of size at most D−1 pays at least 2D−2
boundary edges. The estimate even holds at all sizes from two to D−1. -/
theorem odd_nonsingleton_clique_boundary (Q : SimpleGraph X) (C : Set X) (D : ℕ)
    (reg : ∀x∈C,Nat.card (Q.neighborSet x)=D) (cl : Q.IsClique C)
    (_odd : Odd C.ncard) (lo : 3≤C.ncard) (hi : C.ncard≤D-1) :
    2*D-2≤crossCount Q C Cᶜ := by
  rw [clique_boundary_count Q C D cl reg]
  let a := C.ncard-2
  let b := D-1-C.ncard
  have s : C.ncard=a+2 := by dsimp [a];omega
  have gap : D+1-C.ncard=b+2 := by dsimp [b];omega
  have dec : D=a+b+3 := by dsimp [a,b];omega
  have more : 0≤a*b := Nat.zero_le _
  rw [gap,s,Nat.add_mul,Nat.mul_add]
  omega

#print axioms odd_nonsingleton_clique_boundary
end JSP452Audit.StarHost
