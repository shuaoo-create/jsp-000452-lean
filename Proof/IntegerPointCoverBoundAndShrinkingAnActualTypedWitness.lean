import ARealLargePositiveCoreAndASignedPriceForEveryLegalExteriorCut
namespace JSP452Audit.StarHost
open SimpleGraph

def coveredCoordinateTax (N r x y:ℕ) := (N*(x+y)-(r+1)*x*y)/(x*y+x+y)
def pointCoordinateTax (Z N r x y:ℕ) :=
  max (max (min Z (N/(x+1))) (min Z (N/(y+1)))) (coveredCoordinateTax N r x y)

theorem cover_integer_alternative (N r x y f g:ℕ) (px:0<x) (py:0<y) :
    f+g-1-r≤coveredCoordinateTax N r x y ∨ N-x*f≤coveredCoordinateTax N r x y ∨ N-y*g≤coveredCoordinateTax N r x y := by
  let t := coveredCoordinateTax N r x y
  change _≤t ∨ _≤t ∨ _≤t
  by_contra! bad
  obtain ⟨base,left,right⟩ := bad
  let j := t+1
  have a : x*f+j≤N := by dsimp [j];omega
  have b : y*g+j≤N := by dsimp [j];omega
  have width : j+(r+1)≤f+g := by dsimp [j];omega
  have cost : j*(x*y+x+y)+(r+1)*x*y≤N*(x+y) := calc
    j*(x*y+x+y)+(r+1)*x*y=(j+(r+1))*(x*y)+j*(x+y) := by ring
    _ ≤ (f+g)*(x*y)+j*(x+y) := Nat.add_le_add_right (Nat.mul_le_mul_right _ width) _
    _ = (x*f+j)*y+(y*g+j)*x := by ring
    _ ≤ N*y+N*x := Nat.add_le_add (Nat.mul_le_mul_right _ a) (Nat.mul_le_mul_right _ b)
    _ = N*(x+y) := by ring
  have cash : j*(x*y+x+y)≤N*(x+y)-(r+1)*x*y := by omega
  have limit := (Nat.le_div_iff_mul_le (by omega : 0<x*y+x+y)).mpr cash
  change j≤t at limit
  dsimp [j] at limit;omega

theorem actual_typed_width_down {X:Type*} (G:SimpleGraph X) {x y L l:ℕ}
    (seen:ExactTypedWidth G x y L) (small:l≤L) : ExactTypedWidth G x y l := by
  by_cases zero:l=0
  · exact Or.inl zero
  rcases seen with dead|⟨u,v,up,vp,eq,force⟩
  · omega
  let a := min u l
  let b := l+1-a
  have pa : 0<a := by dsimp only [a];omega
  have pb : 0<b := by dsimp only [a,b];omega
  have la : a≤u := Nat.min_le_left _ _
  have lb : b≤v := by dsimp only [a,b];omega
  refine Or.inr ⟨a,b,pa,pb,by dsimp only [b];omega,?_⟩
  exact forces_uniform_subforests G (fun _:Fin u => x) (fun _:Fin v => y) x y a b
    (by simpa using la) (by simpa using lb) force

#print axioms cover_integer_alternative
#print axioms actual_typed_width_down
end JSP452Audit.StarHost
