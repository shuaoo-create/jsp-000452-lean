import ExceptionalCutPartition
import SplitRootBoundFromFour
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The actual exceptional partition on residual labels is either entirely
singletons, or it has exactly one D−1 clique. In the latter branch the heavy
endpoint touches at least two distinct labels outside that clique. -/
theorem exceptional_original_sizes (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ)) (gap : N.vertsᶜ.ncard+1=I.ncard)
    (anti : (Q.induce Iᶜ).IsClique (mateAntineighborhood (Q.induce Iᶜ) N.vertsᶜ))
    {a b : ↥(Iᶜ : Set X)} (heavy : holeHeavy (Q.induce Iᶜ) N a) (ab : N.Adj a b) :
    let H := Q.induce Iᶜ
    let F := exceptionalParts H N b
    (∀i,(F i).ncard=1) ∨
      ∃k,(F k).ncard=D-1 ∧ (∀i,i≠k → (F i).ncard=1) ∧
        ∃u v,u≠v ∧ u∉F k ∧ v∉F k ∧ H.Adj a u ∧ H.Adj a v := by
  intro H F
  classical
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))
  let _ := Fintype.ofFinite J
  have limit (U : Set ↥(Iᶜ : Set X)) (si : H.IsIndepSet U) : U.ncard≤N.vertsᶜ.ncard+1 := by
    have imageInd : Q.IsIndepSet (Subtype.val '' U) := by
      rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne edge
      exact si hv hw (fun eq => ne (congrArg Subtype.val eq)) edge
    have cap := largest _ imageInd
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap
  obtain ⟨_,dis,cl,odd,away,cover,sep⟩ := exceptional_cut_partition H N hm max limit anti heavy ab
  have sizes (i:Option J) : 1≤(F i).ncard ∧ (F i).ncard≤D-1 := by
    let C := Subtype.val '' F i
    have outside : C⊆Iᶜ := by rintro _ ⟨v,_,rfl⟩;exact v.property
    have ccl : Q.IsClique C := by
      rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ diff
      exact cl i hv hw (fun h => diff (congrArg Subtype.val h))
    have hi := outside_largest_clique_size Q I C ind largest outside ccl D (fun v => (reg v).le)
    rw [show C.ncard=(F i).ncard from Set.ncard_image_of_injective _ Subtype.val_injective] at hi
    have o := Nat.odd_iff.mp (odd i)
    have e := Nat.even_iff.mp par
    change (F i).ncard%2=1 at o
    omega
  have count : I.ncard=Fintype.card (Option J) := by
    rw [Fintype.card_option,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq];exact gap.symm
  by_cases someBig : ∃i:Option J,3≤(F i).ncard
  · right
    obtain ⟨k,big⟩ := someBig
    have exacts := original_split_clique_sizes_from_four Q I ind largest D four reg a F count
      dis away cover cl sep sizes k big
    refine ⟨k,exacts.1,exacts.2,?_⟩
    cases k with
    | none =>
      obtain ⟨u,hu,ua,_⟩ := holeHeavy_exposed_neighbor_ne H N heavy a
      obtain ⟨v,hv,va,vu⟩ := holeHeavy_exposed_neighbor_ne H N heavy u
      have out (w : ↥(Iᶜ : Set X)) (hw:w∉N.verts) : w∉F none := fun h =>
        Set.disjoint_left.mp (dis (some (⟨w,hw⟩:J)) none (by simp)) (mateBlock_self H N w) h
      exact ⟨u,v,vu.symm,out u hu,out v hv,ua.symm,va.symm⟩
    | some j =>
      obtain ⟨u,hu,ua,uj⟩ := holeHeavy_exposed_neighbor_ne H N heavy j.val
      have ub : u≠b := fun eq => hu (eq.symm ▸ N.edge_vert ab.symm)
      let t : J := ⟨u,hu⟩
      have out : u∉F (some j) := fun h => Set.disjoint_left.mp
        (dis (some t) (some j) (fun eq => uj (congrArg Subtype.val (Option.some.inj eq)))) (mateBlock_self H N u) h
      have bout : b∉F (some j) := fun h => Set.disjoint_left.mp (dis none (some j) (by simp))
        (Or.inr (Set.mem_singleton b)) h
      exact ⟨u,b,ub,out,bout,ua.symm,N.adj_sub ab⟩
  · left
    intro i
    have no : ¬3≤(F i).ncard := fun h => someBig ⟨i,h⟩
    have o := Nat.odd_iff.mp (odd i)
    change (F i).ncard%2=1 at o
    omega

#print axioms exceptional_original_sizes
end JSP452Audit.StarHost
