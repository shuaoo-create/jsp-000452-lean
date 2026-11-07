import SingleBlockRestoredWidth
namespace JSP452Audit.StarHost

theorem seven_descent_arithmetic (z b w r L:ℕ) (capacity:17≤z) (stage:6*z+3≤7*b)
    (short:b<z-(r+1)) (weight:2≤w) (larger:z+b+w≤L) :
    let M := (2*z+4)/3
    let t := z-(r+1)
    let l := L-M-t
    2*M<L ∧ 5≤l ∧ (L-z-t)=(l-(z-M)) ∧
    ((L:ℤ)-(z:ℤ)-(b:ℤ)-(w:ℤ))<2*(l:ℤ)-((L-z-t:ℕ):ℤ)-4 := by
  dsimp only
  omega

#print axioms seven_descent_arithmetic
end JSP452Audit.StarHost
