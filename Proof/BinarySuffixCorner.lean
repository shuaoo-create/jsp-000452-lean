import DegreeTwoStrictSource
import BinaryRowProfile
namespace JSP452Audit.StarHost
open SimpleGraph
theorem binary_suffix_eq (p a i : ℕ) (head : i<p) :
    (fun k : Fin (p-i+a) => padDemand (binaryProfile p a) (i+k.val))=binaryProfile (p-i) a := by
  funext k
  have li : i+k.val<p+a := by have h:=k.isLt; omega
  rw [padDemand,dif_pos li]
  unfold binaryProfile
  split_ifs <;> simp_all <;> omega

/-- A pair of still-two-leaf heads realizes the *entire* row energy in its
ordinary pair of suffix forests, including both possibly empty unit tails. -/
theorem binary_corner_reduction {X : Type*} [Finite X] (G : SimpleGraph X)
    (p a q b r i j : ℕ) (hi : i<p) (hj : j<q) (idx : i+j=r)
    (row : ForcingRow G (p+a) (q+b) (padDemand (binaryProfile p a)) (padDemand (binaryProfile q b)) r) :
    Forces G (forest (binaryProfile (p-i) a)) (forest (binaryProfile (q-j) b)) ∧
      rowEnergy (binaryProfile p a) (binaryProfile q b) r =
        3*((p-i)+(q-j)-1)+2*max a b+min a b := by
  have old := row i j (p-i+a) (q-j+b) idx (by omega) (by omega) (by omega) (by omega)
  unfold suffixStars at old
  rw [binary_suffix_eq p a i hi,binary_suffix_eq q b j hj] at old
  refine ⟨old,?_⟩
  rw [binary_row_energy (by omega) (by omega) a b r (by omega)]
  omega

#print axioms binary_suffix_eq
#print axioms binary_corner_reduction
end JSP452Audit.StarHost