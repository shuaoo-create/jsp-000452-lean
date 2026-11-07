import PreferredBoundaryProfile
namespace JSP452Audit.StarHost

/-- After singleton holes have paid D apiece, the detached nontrivial
blocks spend against exactly one remaining unit of D in the root budget. -/
theorem active_boundary_price (D k B : ℕ) (six : 6≤D) (pos : 1≤k) (floor : D+1≤B)
    (budget : B+(k-1)*(2*D-2)≤D*(k+1)) : k≤2 ∧ (2*D-1≤B → k=1) := by
  let h:=k-1
  have kh : k=h+1 := by dsimp [h];omega
  have block : 2*D-2=D+(D-2) := by omega
  have rhs : D*(k+1)=h*D+2*D := by
    rw [kh,show h+1+1=h+2 by omega,Nat.mul_add,Nat.mul_comm D h,Nat.mul_comm D 2]
  have lhs : (k-1)*(2*D-2)=h*D+h*(D-2) := by dsimp [h];rw [block,Nat.mul_add]
  rw [lhs,rhs] at budget
  constructor
  · by_contra! big
    have lo := Nat.mul_le_mul_right (D-2) (show 2≤h by omega)
    omega
  · intro high
    by_contra! ne
    have lo := Nat.mul_le_mul_right (D-2) (show 1≤h by omega)
    omega

#print axioms active_boundary_price
end JSP452Audit.StarHost
