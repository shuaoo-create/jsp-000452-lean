import FourRegularGreedyDomination
import DegreeSplitEnvelope
namespace JSP452Audit.StarHost
open SimpleGraph

private theorem layer_card_sum {X L : Type*} [Finite X] [Fintype L] (S:Set (X×L)) :
    (∑l:L,({x:X | (x,l)∈S}:Set X).ncard)=S.ncard := by
  let P := Σl:L,↥({x:X | (x,l)∈S}:Set X)
  let code (p:P) : ↥S := ⟨(p.2.val,p.1),p.2.property⟩
  let dec (s:↥S) : P := ⟨s.val.2,⟨s.val.1,s.property⟩⟩
  let e : P ≃ ↥S := ⟨code,dec,fun _ => rfl,fun _ => rfl⟩
  have eq := Nat.card_congr e
  change Nat.card (Σl:L,↥({x:X | (x,l)∈S}:Set X))=Nat.card ↥S at eq
  simp only [Nat.card_sigma,Nat.card_coe_set_eq] at eq
  exact eq

/-- A full vertex of the base graph has no vertical neighbours in its
regular envelope. Projecting the smallest layer meets all original full
closed neighbourhoods and keeps the average bound. -/
theorem four_partial_domination {X : Type*} [Finite X] (G : SimpleGraph X)
    (cap : ∀v,Nat.card (G.neighborSet v)≤4) :
    ∃S:Set X,(∀v,Nat.card (G.neighborSet v)=4 → v∈S ∨ ∃w∈S,G.Adj v w) ∧ 13*S.ncard≤5*Nat.card X := by
  classical
  let _ := Fintype.ofFinite X
  let L := Layer 4
  let Q := regularEnvelope G 4
  have reg (z:X×L) : Nat.card (Q.neighborSet z)=4 := regularEnvelope_degree G 4 cap z.1 z.2
  obtain ⟨S,hit,cost⟩ := four_regular_greedy_dominates Q reg
  let fiber (l:L) : Set X := {x | (x,l)∈S}
  have total : (∑l:L,(fiber l).ncard)=S.ncard := layer_card_sum S
  have small : ∃l:L,13*(fiber l).ncard≤5*Nat.card X := by
    by_contra! none
    let zero : L := fun _ => false
    have sum := Finset.sum_lt_sum (s:=(Finset.univ : Finset L)) (fun l _ => (none l).le)
      ⟨zero,Finset.mem_univ _,none zero⟩
    rw [show (∑l:L,13*(fiber l).ncard)=13*∑l:L,(fiber l).ncard from (Finset.mul_sum _ _ _).symm,total,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul] at sum
    change 13*S.ncard≤5*Nat.card (X×L) at cost
    rw [Nat.card_prod] at cost
    have same : Nat.card L*(5*Nat.card X)=5*(Nat.card X*Nat.card L) := by ring
    exact (not_lt_of_ge cost) (by simpa only [Nat.cast_id,same] using sum)
  obtain ⟨l,bound⟩ := small
  refine ⟨fiber l,?_,bound⟩
  intro v degree
  rcases hit (v,l) with here|⟨⟨w,j⟩,inside,edge⟩
  · exact Or.inl here
  · rcases edge with ⟨adj,same⟩|⟨_,i,_⟩
    · change l=j at same;subst j
      exact Or.inr ⟨w,inside,adj⟩
    · have impossible := i.isLt
      change i.val<4-Nat.card (G.neighborSet v) at impossible
      omega

#print axioms four_partial_domination
end JSP452Audit.StarHost
