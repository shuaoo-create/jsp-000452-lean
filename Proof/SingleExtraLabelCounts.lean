import EvenLabelOwnersAtPositiveCap
import Mathlib.Combinatorics.SimpleGraph.Sum
namespace JSP452Audit.StarHost.PairedLayers
open SimpleGraph

theorem sum_left_fiber_card {A:Type*} {p:A→Prop} {q:A⊕Unit→Prop}
    (left:∀a,p a ↔ q (.inl a)) (right:¬q (.inr ())) :
    Nat.card {a:A // p a}=Nat.card {z:A⊕Unit // q z} := by
  let f (a:{a:A // p a}) : {z:A⊕Unit // q z} := ⟨.inl a.val,(left a.val).mp a.property⟩
  apply Nat.card_congr (Equiv.ofBijective f ⟨?_,?_⟩)
  · exact fun _ _ e => Subtype.ext (Sum.inl.inj (congrArg Subtype.val e))
  · rintro ⟨a|⟨⟩,h⟩
    · exact ⟨⟨a,(left a).mpr h⟩,rfl⟩
    · exact (right h).elim

def paddedTip {A X:Type*} (t:A→X) : A⊕Unit→X⊕Unit := Sum.map t id

theorem padded_port_budget {A X:Type*} [Finite A] [Finite X] (k:ℕ) (Q:SimpleGraph X) (t:A→X)
    (cap:∀v,Nat.card (Q.neighborSet v)+Nat.card {a:A // t a=v}≤2*(k+1)) (v:X⊕Unit) :
    Nat.card (((Q ⊕g (⊥:SimpleGraph Unit)).neighborSet v))+Nat.card {a:A⊕Unit // paddedTip t a=v}≤2*(k+1) := by
  cases v with
  | inl x =>
    have deg := sum_left_fiber_card (p:=fun y => Q.Adj x y)
      (q:=fun z => (Q ⊕g (⊥:SimpleGraph Unit)).Adj (.inl x) z) (fun _ => Iff.rfl) (by simp)
    have labels := sum_left_fiber_card (p:=fun a => t a=x) (q:=fun z => paddedTip t z=.inl x)
      (fun _ => by simp [paddedTip]) (by simp [paddedTip])
    change Nat.card (Q.neighborSet x)=Nat.card ((Q ⊕g (⊥:SimpleGraph Unit)).neighborSet (.inl x)) at deg
    rw [←deg,←labels];exact cap x
  | inr u =>
    have zero : ((Q ⊕g (⊥:SimpleGraph Unit)).neighborSet (.inr u))=∅ := by
      ext z;cases z <;> simp [SimpleGraph.mem_neighborSet]
    have point : {a:A⊕Unit|paddedTip t a=.inr u}=({.inr ()}:Set _) := by
      ext z;cases u;cases z with
      | inl a => simp [paddedTip]
      | inr w => cases w;simp [paddedTip]
    have one := congrArg Set.ncard point
    rw [Set.ncard_singleton] at one
    change Nat.card {a:A⊕Unit // paddedTip t a=.inr u}=1 at one
    rw [zero,Nat.card_coe_set_eq,Set.ncard_empty,one];omega

theorem single_extra_parity {A:Type*} [Finite A] {m:ℕ} (c:A⊕Unit→Fin m)
    (even:∀j,Even (({b:A⊕Unit|c b=j}:Set _).ncard)) :
    (Finset.univ.filter (fun j => Odd (({a:A|c (.inl a)=j}:Set _).ncard))).card≤1 := by
  classical
  have sub : (Finset.univ.filter (fun j => Odd (({a:A|c (.inl a)=j}:Set _).ncard))) ⊆ {c (.inr ())} := by
    intro j hj
    have odd := (Finset.mem_filter.mp hj).2
    by_contra missing
    have diff : c (.inr ())≠j := by simpa [eq_comm] using missing
    have equal := sum_left_fiber_card (p:=fun a => c (.inl a)=j) (q:=fun z => c z=j) (fun _ => Iff.rfl) diff
    change ({a:A|c (.inl a)=j}:Set _).ncard=({z:A⊕Unit|c z=j}:Set _).ncard at equal
    exact (Nat.not_even_iff_odd.mpr odd) (equal.symm ▸ even j)
  simpa using Finset.card_le_card sub

#print axioms sum_left_fiber_card
#print axioms padded_port_budget
#print axioms single_extra_parity
end JSP452Audit.StarHost.PairedLayers
