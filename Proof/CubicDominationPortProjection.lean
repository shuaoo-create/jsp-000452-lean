import CubicRegularTwoFifths
import DegreeSplitEnvelope
import FourExteriorPorts
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
cubic regular envelope. Projecting the smallest layer meets all original full
closed neighbourhoods and keeps the average bound. -/
theorem cubic_partial_domination {X : Type*} [Finite X] (G : SimpleGraph X)
    (cap : ∀v,Nat.card (G.neighborSet v)≤3) :
    ∃S:Set X,(∀v,Nat.card (G.neighborSet v)=3 → v∈S ∨ ∃w∈S,G.Adj v w) ∧ 5*S.ncard≤2*Nat.card X := by
  classical
  let _ := Fintype.ofFinite X
  let L := Layer 3
  let Q := regularEnvelope G 3
  have reg (z:X×L) : Nat.card (Q.neighborSet z)=3 := regularEnvelope_degree G 3 cap z.1 z.2
  obtain ⟨S,hit,cost⟩ := cubic_regular_two_fifths Q reg
  let fiber (l:L) : Set X := {x | (x,l)∈S}
  have total : (∑l:L,(fiber l).ncard)=S.ncard := layer_card_sum S
  have small : ∃l:L,5*(fiber l).ncard≤2*Nat.card X := by
    by_contra! none
    let zero : L := fun _ => false
    have sum := Finset.sum_lt_sum (s:=(Finset.univ : Finset L)) (fun l _ => (none l).le)
      ⟨zero,Finset.mem_univ _,none zero⟩
    rw [show (∑l:L,5*(fiber l).ncard)=5*∑l:L,(fiber l).ncard from (Finset.mul_sum _ _ _).symm,total,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul] at sum
    change 5*S.ncard≤2*Nat.card (X×L) at cost
    rw [Nat.card_prod] at cost
    have same : Nat.card L*(2*Nat.card X)=2*(Nat.card X*Nat.card L) := by ring
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
      change i.val<3-Nat.card (G.neighborSet v) at impossible
      omega

/-- Adjoin precisely the exterior labels seen by the target vertices.
All their original neighbours survive. The regular envelope projection
therefore gives a genuine dominating set in the original graph. -/
theorem cubic_dominates_via_actual_ports {X : Type*} [Finite X] (G : SimpleGraph X) (Y B T : Set X)
    (apart : Disjoint Y B) (cover : Y∪B=Set.univ) (sub : T⊆Y)
    (full : ∀v∈T,Nat.card (G.neighborSet v)=3) (cap : ∀v,Nat.card (G.neighborSet v)≤3) :
    ∃S:Set X,(∀v∈T,v∈S ∨ ∃w∈S,G.Adj v w) ∧ 5*S.ncard≤2*(Y.ncard+crossCount G T B) := by
  classical
  let P := {w | w∈B ∧ ∃v∈T,G.Adj v w}
  let W := Y∪P
  have countP : P.ncard≤crossCount G T B := exterior_port_count G T B
  have pB : P⊆B := fun _ h => h.1
  have dis : Disjoint Y P := apart.mono_right pB
  have capW (w:↥W) : Nat.card ((G.induce W).neighborSet w)≤3 :=
    (induced_neighbor_count_le G W w).trans (cap _)
  have here (v:X) (hv:v∈T) (w:X) (adj:G.Adj v w) : w∈W := by
    rcases (show w∈Y∪B from cover.symm ▸ Set.mem_univ w) with y|b
    · exact Or.inl y
    · exact Or.inr ⟨b,v,hv,adj⟩
  have degree (v:X) (hv:v∈T) : Nat.card ((G.induce W).neighborSet ⟨v,Or.inl (sub hv)⟩)=3 := by
    let y : W := ⟨v,Or.inl (sub hv)⟩
    let f (w:G.neighborSet v) : (G.induce W).neighborSet y := ⟨⟨w.val,here v hv _ w.property⟩,w.property⟩
    have up := Nat.card_le_card_of_injective f (fun a b eq => Subtype.ext (congrArg
      (fun z:(G.induce W).neighborSet y => z.val.val) eq))
    rw [full v hv] at up
    exact le_antisymm (capW y) up
  obtain ⟨S,hit,cost⟩ := cubic_partial_domination (G.induce W) capW
  let chosen := Subtype.val '' S
  have size : chosen.ncard=S.ncard := Set.ncard_image_of_injective S Subtype.val_injective
  refine ⟨chosen,?_,?_⟩
  · intro v hv
    rcases hit ⟨v,Or.inl (sub hv)⟩ (degree v hv) with sel|⟨w,sel,adj⟩
    · exact Or.inl ⟨_,sel,rfl⟩
    · exact Or.inr ⟨w.val,⟨w,sel,rfl⟩,adj⟩
  · rw [size]
    rw [Nat.card_coe_set_eq] at cost
    change 5*S.ncard≤2*(Y∪P).ncard at cost
    rw [Set.ncard_union_eq dis] at cost
    omega

#print axioms cubic_partial_domination
#print axioms cubic_dominates_via_actual_ports
end JSP452Audit.StarHost
