import SmallAlphaPerfect
import EnvelopeComponentSum
import ZhaoFamilyBudget
open private JSP452Audit.StarHost.cut_neighbor_account from ZhaoFamilyBudget

namespace JSP452Audit.StarHost
open SimpleGraph

private theorem ah_component_degree_bound {X : Type*} [Finite X]
    (G : SimpleGraph X) (S : Set X) (c : (G.induce Sᶜ).ConnectedComponent)
    (x : c.supp) :
    Nat.card (G.neighborSet x.val.val)+1 ≤ S.ncard+c.supp.ncard := by
  have cut := JSP452Audit.StarHost.cut_neighbor_account G S x.val
  have removed := Set.ncard_le_ncard (show G.neighborSet x.val.val ∩ S ⊆ S from Set.inter_subset_right)
  have internal := Set.ncard_le_ncard
    (show c.toSimpleGraph.neighborSet x ⊆ ({x} : Set c.supp)ᶜ from
      fun y h => fun same => (@SimpleGraph.Adj.ne _ c.toSimpleGraph x y h) (Set.mem_singleton_iff.mp same).symm)
  rw [Set.ncard_compl,Set.ncard_singleton] at internal
  have present : 0<c.supp.ncard := (Set.ncard_pos (Set.toFinite _)).mpr c.nonempty_supp
  change (c.toSimpleGraph.neighborSet x).ncard ≤ c.supp.ncard-1 at internal
  rw [←Nat.card_coe_set_eq,component_degree_eq] at internal
  omega

private noncomputable def ah_oddRep {Y : Type*} (H : SimpleGraph Y) (c : H.oddComponents) : Y :=
  c.val.nonempty_supp.choose

private theorem ah_oddRep_tag {Y : Type*} (H : SimpleGraph Y) (c : H.oddComponents) :
    H.connectedComponentMk (ah_oddRep H c)=c.val :=
  c.val.nonempty_supp.choose_spec

private theorem ah_oddRep_injective {Y : Type*} (H : SimpleGraph Y) :
    Function.Injective (ah_oddRep H) := by
  intro c d same
  apply Subtype.ext
  rw [←ah_oddRep_tag H c,←ah_oddRep_tag H d,same]

/-- An even graph whose minimum degree is one below half its order still
has a perfect matching if at most half its vertices attain that low degree. -/
theorem almost_half_degree_perfect {X : Type*} [Finite X] (G : SimpleGraph X)
    (r : ℕ) (positive : 0<r) (order : Nat.card X=2*r)
    (minimum : ∀ x, r-1≤Nat.card (G.neighborSet x))
    (lowCount : {x | Nat.card (G.neighborSet x)=r-1}.ncard≤r) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  apply G.tutte.mpr
  intro S
  rw [tutte_violator_induce]
  intro violation
  let H := G.induce Sᶜ
  let q := H.oddComponents.ncard
  let s := S.ncard
  have total : s+Nat.card ↥(Sᶜ : Set X)=2*r := by
    simpa only [Nat.card_coe_set_eq,order] using Set.ncard_add_ncard_compl S
  have parity := H.odd_ncard_oddComponents
  simp only [Nat.odd_iff,Nat.card_coe_set_eq] at parity
  have many : s+2≤q := by
    change S.ncard<H.oddComponents.ncard at violation
    
    have total' : S.ncard+Sᶜ.ncard=2*r := by simpa only [Nat.card_coe_set_eq] using total
    dsimp [q,s]; omega
  have qCap : q≤Nat.card ↥(Sᶜ : Set X) :=
    Nat.card_le_card_of_injective (ah_oddRep H) (ah_oddRep_injective H)
  have smallS : s≤r-1 := by omega
  have componentMin (c : H.ConnectedComponent) : r-s≤c.supp.ncard := by
    let x : c.supp := c.nonempty_supp.to_subtype.some
    have degree := ah_component_degree_bound G S c x
    have base := minimum x.val.val
    dsimp [s]; omega
  let _ := Fintype.ofFinite H.oddComponents
  let label (v : Σ c : H.oddComponents, c.val.supp) : ↥(Sᶜ : Set X) := v.2.val
  have labelInj : Function.Injective label := by
    rintro ⟨c,x⟩ ⟨d,y⟩ same
    change x.val=y.val at same
    have cd : c=d := Subtype.ext (x.property.symm.trans ((congrArg H.connectedComponentMk same).trans y.property))
    subst d
    congr 1
    exact Subtype.ext same
  have sumCap : (∑ c : H.oddComponents, Nat.card c.val.supp) ≤ Nat.card ↥(Sᶜ : Set X) := by
    rw [←Nat.card_sigma]
    exact Nat.card_le_card_of_injective label labelInj
  have eachSum := Finset.sum_le_sum (s:=Finset.univ)
    (fun (c : H.oddComponents) _ => componentMin c.val)
  have multiplied : q*(r-s) ≤ Nat.card ↥(Sᶜ : Set X) := by
    have count : Fintype.card H.oddComponents=q := (Nat.card_eq_fintype_card (α:=H.oddComponents)).symm
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,count] using eachSum.trans (by simpa only [Nat.card_coe_set_eq] using sumCap)
  have budget : s+(s+2)*(r-s)≤2*r := by
    have m := Nat.mul_le_mul_right (r-s) many
    omega
  have endpoints : s=0 ∨ s=r-1 := by
    by_cases empty : s=0
    · exact Or.inl empty
    · right
      by_contra other
      have lo : 1≤s := by omega
      have hi : 2≤r-s := by omega
      have sum : s+(r-s)=r := Nat.add_sub_of_le (by omega)
      rw [Nat.add_mul,Nat.two_mul] at budget
      have more := Nat.mul_le_mul_left s hi
      rw [Nat.mul_two] at more
      omega
  rcases endpoints with empty | large
  · have allLow (x : X) : Nat.card (G.neighborSet x)=r-1 := by
      have emptyS : S=∅ := (Set.ncard_eq_zero (Set.toFinite S)).mp empty
      let v : ↥(Sᶜ : Set X) := ⟨x,by simp [emptyS]⟩
      let c := H.connectedComponentMk v
      have another : ∃ d∈H.oddComponents, d≠c := by
        by_contra! none
        have atMost : H.oddComponents.ncard≤1 :=
          (Set.ncard_le_one (Set.toFinite _)).mpr (fun a ha b hb => (none a ha).trans (none b hb).symm)
        dsimp [q] at many; omega
      obtain ⟨d,hd,dc⟩ := another
      have apart : Disjoint c.supp d.supp := Set.disjoint_left.mpr (by
        intro z zc zd
        exact dc (zd.symm.trans zc))
      have combined : c.supp.ncard+d.supp.ncard≤Nat.card ↥(Sᶜ : Set X) := by
        rw [←Set.ncard_union_eq apart]
        exact Set.ncard_le_card _
      have dMin := componentMin d
      have bound := ah_component_degree_bound G S c (⟨v,rfl⟩ : c.supp)
      have base := minimum x
      change Nat.card (G.neighborSet x)+1≤s+c.supp.ncard at bound
      omega
    have allSet : {x | Nat.card (G.neighborSet x)=r-1}=Set.univ := by ext; simp [allLow]
    rw [allSet,Set.ncard_univ,order] at lowCount
    omega
  · have sameCard : Nat.card H.oddComponents=Nat.card ↥(Sᶜ : Set X) := by
      change q=_
      omega
    have surj := (Nat.bijective_iff_injective_and_card (ah_oddRep H)).mpr
      ⟨ah_oddRep_injective H,sameCard⟩ |>.2
    have edgeless : ∀ x y, ¬H.Adj x y := by
      intro x y edge
      obtain ⟨c,rfl⟩ := surj x
      obtain ⟨d,rfl⟩ := surj y
      have same : c=d := Subtype.ext
        ((ah_oddRep_tag H c).symm.trans ((ConnectedComponent.sound edge.reachable).trans (ah_oddRep_tag H d)))
      exact edge.ne (congrArg (ah_oddRep H) same)
    have allLow (x : ↥(Sᶜ : Set X)) : Nat.card (G.neighborSet x.val)=r-1 := by
      have emptyNeigh : H.neighborSet x=∅ := by ext y; simp [edgeless]
      have cut := JSP452Audit.StarHost.cut_neighbor_account G S x
      change Nat.card (H.neighborSet x)+_=_ at cut
      rw [emptyNeigh,Nat.card_coe_set_eq,Set.ncard_empty,zero_add] at cut
      have removed := Set.ncard_le_ncard (show G.neighborSet x.val ∩ S ⊆ S from Set.inter_subset_right)
      have base := minimum x.val
      change s=r-1 at large
      omega
    let lowLabel (x : ↥(Sᶜ : Set X)) : {x | Nat.card (G.neighborSet x)=r-1} := ⟨x.val,allLow x⟩
    have lowInj : Function.Injective lowLabel := fun _ _ eq => Subtype.ext (congrArg (fun z : {x | Nat.card (G.neighborSet x)=r-1} => z.val) eq)
    have tooMany := Nat.card_le_card_of_injective lowLabel lowInj
    simp only [Nat.card_coe_set_eq] at tooMany total lowCount
    omega

#print axioms almost_half_degree_perfect
end JSP452Audit.StarHost

