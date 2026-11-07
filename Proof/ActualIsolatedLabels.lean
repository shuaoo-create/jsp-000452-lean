import GreedyIndependent
import RobustHalfOrderGap
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Original neighbours of an independently chosen set can be deleted
without deleting the set. The size is bounded by the sum of original degrees. -/
theorem independent_open_neighborhood (H : SimpleGraph X) (D : ℕ) (I : Set X)
    (ind : H.IsIndepSet I) (cap : ∀v,Nat.card (H.neighborSet v)≤D) :
    ∃N:Set X, N⊆Iᶜ ∧ N.ncard≤D*I.ncard ∧ ∀i∈I,∀v,H.Adj i v → v∈N := by
  classical
  let N := {v | ∃i∈I,H.Adj i v}
  have dis : N⊆Iᶜ := by
    rintro v ⟨i,mem,adj⟩ inside
    exact ind mem inside adj.ne adj
  let _ := Fintype.ofFinite I
  have witness (v:N) : ∃i:I,H.Adj i.val v.val := by
    obtain ⟨i,mem,e⟩ := v.property;exact ⟨⟨i,mem⟩,e⟩
  let P := Σi:I,H.neighborSet i.val
  let pack (v:N) : P := ⟨(witness v).choose,⟨v.val,(witness v).choose_spec⟩⟩
  have count := Nat.card_le_card_of_injective pack (fun a b eq => Subtype.ext
    (congrArg (fun u:P => (u.2:X)) eq))
  change Nat.card N≤Nat.card (Σi:I,H.neighborSet i.val) at count
  rw [Nat.card_sigma,Nat.card_coe_set_eq] at count
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun (v:I) _ => cap v.val)
  have card : Fintype.card I=I.ncard := (Nat.card_eq_fintype_card (α:=I)).symm
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card] at sum
  exact ⟨N,dis,count.trans (sum.trans_eq (Nat.mul_comm _ _)),fun i h v e => ⟨i,h,e⟩⟩

/-- In the actual core remove exactly b labels, isolating floor(b/D)
other labels in the surviving graph. -/
theorem deletion_isolates_labels (H : SimpleGraph X) {D b μ : ℕ} (pos : 0<D)
    (cap : ∀v,Nat.card (H.neighborSet v)≤D) (short : b<μ) (order : 2*μ≤Nat.card X) :
    ∃I U:Set X, I.ncard=b/D ∧ U.ncard=b ∧ U⊆Iᶜ ∧ ∀i∈I,∀v,H.Adj i v → v∈U := by
  classical
  let j := b/D
  have dj : D*j≤b := by rw [Nat.mul_comm];exact Nat.div_mul_le_self _ _
  have jle : j≤b := Nat.div_le_self _ _
  have enough : (D+1)*j<(Set.univ:Set X).ncard := by
    rw [Nat.add_mul,Nat.one_mul,Set.ncard_univ];omega
  obtain ⟨I,_,ind,count⟩ := greedy_independent_exact H D j j Set.univ cap enough (by omega)
  obtain ⟨N,dis,size,all⟩ := independent_open_neighborhood H D I ind cap
  rw [count] at size
  have avail : b≤Iᶜ.ncard := by
    have tot := Set.ncard_add_ncard_compl I
    omega
  obtain ⟨U,left,right,uc⟩ := Set.exists_subsuperset_card_eq dis (size.trans dj) avail
  exact ⟨I,U,count,uc,right,fun i hi v adj => left (all i hi v adj)⟩

#print axioms independent_open_neighborhood
#print axioms deletion_isolates_labels
end JSP452Audit.StarHost
