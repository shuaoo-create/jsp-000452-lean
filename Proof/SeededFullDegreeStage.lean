import ThreeOtherPositiveBlocks
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem extend_full_degree_stage {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) (J:Set X)
    (ind:G.IsIndepSet J) (full:∀x∈J,Nat.card (G.neighborSet x)=D) :
    ∃B:Set X,J⊆B ∧ CompleteDegreeStage G D B := by
  classical
  let available := {x:X|x∉J ∧ ∀y∈J,¬G.Adj x y}
  obtain ⟨I,inc,degree,indI,dom⟩ := choose_full_exterior_independent G available D
  refine ⟨J∪I,Set.subset_union_left,?_,?_,?_⟩
  · intro x hx y hy ne edge
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · exact ind hx hy ne edge
    · exact (inc hy).2 x hx edge.symm
    · exact (inc hx).2 y hy edge
    · exact indI hx hy ne edge
  · intro x hx;exact hx.elim (full x) (degree x)
  · intro x deg
    by_cases inside:x∈J
    · exact Or.inl (Or.inl inside)
    by_cases adj:∃y∈J,G.Adj x y
    · obtain ⟨y,hy,e⟩ := adj
      exact Or.inr ⟨y,Or.inl hy,e⟩
    have avail : x∈available := ⟨inside,fun y hy e => adj ⟨y,hy,e⟩⟩
    obtain hx|⟨y,hy,e⟩ := dom x avail deg
    · exact Or.inl (Or.inr hx)
    · exact Or.inr ⟨y,Or.inr hy,e⟩

theorem strict_seven_seeded_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) (p:↥K.positive)
    (smallest:∀q:↥K.positive,K.pieceCapacity p≤K.pieceCapacity q) :
    let H := F.G \ wholePiece F.G K.barrier p.val
    ∃E B:Set F.X,6*K.pieceCapacity p+3≤E.ncard ∧ (∀x∈E,Nat.card (H.neighborSet x)=7) ∧
      CompleteDegreeStage H 7 B ∧ 6*K.pieceCapacity p+3≤7*B.ncard := by
  intro H
  obtain ⟨E,J,size,full,sub,ind,room,_⟩ := three_other_seven_blocks F paid seven K p smallest
  obtain ⟨B,inc,stage⟩ := extend_full_degree_stage H 7 J ind (fun x hx => full x (sub hx))
  have more := Set.ncard_le_ncard inc
  exact ⟨E,B,size,full,stage,by omega⟩

#print axioms extend_full_degree_stage
#print axioms strict_seven_seeded_stage
end JSP452Audit.StarHost
