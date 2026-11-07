import OddCoverage
import CoreIdentity
import CoreCounts
namespace JSP452Audit.Padded
open SimpleGraph
variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

private theorem range_count {I Z : Type*} [Finite I] (f : I → Z) :
    (Set.range f).ncard ≤ Nat.card I := by
  apply Nat.card_le_card_of_surjective (Set.rangeFactorization f)
  rintro ⟨_,i,rfl⟩
  exact ⟨i,rfl⟩

theorem Spec.odd_canonical_upper {S T : Set V} (dis : Disjoint S T) :
    (P.canonGraph S T).oddComponents.ncard ≤ Nat.card (P.SingletonIndex S T) + (P.tightOdd S T).ncard + 1 := by
  classical
  let H := P.canonGraph S T
  let single (z : {z : P.Vertex // P.singletonLabel S T z}) :=
    H.connectedComponentMk (P.canonicalPoint z.val (P.singletonLabel_kept dis z.property))
  let core (C : P.tightOdd S T) := P.coreCC C.val
  let pool := P.canonPoolComponents S T
  have covers : H.oddComponents ⊆ (Set.range single ∪ Set.range core) ∪ pool := by
    intro c hc
    rcases P.canonical_odd_covered dis c hc with ⟨z,hs,hm⟩ | ⟨C,z,hz,hm⟩ | pooled
    · exact Or.inl (Or.inl ⟨⟨z.val,hs⟩,hm⟩)
    · have idcc : c=P.coreCC C := (show H.connectedComponentMk z=c from hm).symm.trans (P.has_core_cc hz)
      by_cases tight : P.coreTight C
      · have card : (P.coreCC C).supp.ncard = Nat.card {v : P.Vertex // P.onCore C v} :=
          Nat.card_congr (P.tightFiberEquiv dis tight)
        have odd : Odd ((P.coreCC C).supp.ncard) := idcc ▸ hc
        exact Or.inl (Or.inr ⟨⟨C,tight,card ▸ odd⟩,idcc.symm⟩)
      · obtain ⟨a,w,_,lab,inCore,inPool⟩ := P.exists_core_optional_of_not_tight C tight
        exact Or.inr ⟨w,.inl (.inr a),lab,inPool,(P.has_core_cc inCore).trans idcc.symm⟩
    · exact Or.inr pooled
  have ub := (Set.ncard_le_ncard covers).trans (Set.ncard_union_le (Set.range single ∪ Set.range core) pool)
  have pair := Set.ncard_union_le (Set.range single) (Set.range core)
  have sb := range_count single
  have cb := range_count core
  have sEq := Nat.card_congr (P.singletonIndexEquiv S T)
  have poolSize : pool.ncard ≤ 1 := P.canonPool_at_most_one S T
  change (Set.range core).ncard ≤ (P.tightOdd S T).ncard at cb
  change H.oddComponents.ncard ≤ _
  omega

#print axioms Spec.odd_canonical_upper
end JSP452Audit.Padded
