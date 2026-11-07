import SingleEscapeMixedRectangle
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def SingleUnpaidKinds {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (ht:0<t) (r : ℕ) : Prop :=
  ∀j x y, UnpaidHeight G K n m r j → WinsHeight n m r j x y →
    (y=1 ∧ x=j) ∨
    (x=2 ∧ (∑i,(n i-1)/2)<originalThresholdCount n 2 ∧
      ((y=2 ∧ j=3) ∨ (y=m ⟨0,ht⟩ ∧ j=m ⟨0,ht⟩+1)))

private theorem classify_unpaid {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r d : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (mass : (∑i,m i)+d≤matchingEdges (G.induce K.core)+K.roots.ncard+minimumExposure G D)
    (reserve : minimumExposure G D+1≤d)
    (exterior : r+2*(d+∑i,(m i-1)/2)≤s-matchingEdges (G.induce K.core))
    (esc : matchingEdges (G.induce K.core)<s) : SingleUnpaidKinds G K n m ht r := by
  intro j x y loss win
  have eq := win.2.2.1
  have pos := win.2.1
  by_cases unit : y=1
  · exact Or.inl ⟨unit,by omega⟩
  obtain ⟨two,large,bound⟩ := single_escape_unpaid_rectangle G K n m r d j x y hs ht hn hm pn pm
    endpoint mass reserve exterior esc loss win (by omega)
  exact Or.inr ⟨two,large,bound.imp (fun b => ⟨b,by omega⟩) id⟩

/-- At any unpaid height in a single escape, every winner is classified:
pure escaping axis, mixed 2 versus 2 at height three, or 2 versus the
largest opposite head at the boundary immediately above it. -/
theorem strict_single_unpaid_types (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    (μ<F.s → F.t≤μ → SingleUnpaidKinds F.G K F.n F.m F.ht F.r) ∧
    (μ<F.t → F.s≤μ → SingleUnpaidKinds F.G K F.m F.n F.hs F.r) := by
  intro μ
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  let a := K.roots.ncard
  obtain ⟨nl,ml⟩ := strict_source_whole_list_alternatives F K
  obtain ⟨red,blue⟩ := original_root_endpoint_guards F paid K
  obtain ⟨outerR,outerB⟩ := strict_exterior_endpoint_guards F paid K
  have cover : minimumExposure F.G D+1≤d := (minimal_strict_source_deficit F paid).2.1
  have places := nontrivial_core_count_le_region_pieces F.G _ K
  change nontrivialCoreCount (F.G.induce K.core)≤a+minimumExposure F.G D at places
  constructor
  · intro escaped inside
    obtain ⟨_,weight,_⟩ := ml.resolve_left (by change ¬μ+d+1≤F.t;omega)
    change (∑j,F.m j)+d≤μ+nontrivialCoreCount (F.G.induce K.core) at weight
    have strength := outerR escaped
    change a+F.r+2*(d+∑j,(F.m j-1)/2)+_≤F.s-μ at strength
    exact classify_unpaid F.G K F.n F.m F.r d F.hs F.ht F.hn F.hm F.pn F.pm red
      (by change (∑j,F.m j)+d≤μ+a+minimumExposure F.G D;omega) cover
      (by change F.r+2*(d+∑j,(F.m j-1)/2)≤F.s-μ;omega) escaped
  · intro escaped inside
    obtain ⟨_,weight,_⟩ := nl.resolve_left (by change ¬μ+d+1≤F.s;omega)
    change (∑i,F.n i)+d≤μ+nontrivialCoreCount (F.G.induce K.core) at weight
    have strength := outerB escaped
    change a+F.r+2*(d+∑i,(F.n i-1)/2)+_≤F.t-μ at strength
    exact classify_unpaid F.G K F.m F.n F.r d F.ht F.hs F.hm F.hn F.pm F.pn blue
      (by change (∑i,F.n i)+d≤μ+a+minimumExposure F.G D;omega) cover
      (by change F.r+2*(d+∑i,(F.n i-1)/2)≤F.t-μ;omega) escaped

/-- An arbitrary single escaping side must exhibit at least one
actual unpaid winning pair, and every winner has the listed form. -/
theorem strict_single_escape_winner (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    (μ<F.s → F.t≤μ → MissingHeightWitness F.G K F.n F.m F.r ∧ SingleUnpaidKinds F.G K F.n F.m F.ht F.r) ∧
    (μ<F.t → F.s≤μ → MissingHeightWitness F.G K F.m F.n F.r ∧ SingleUnpaidKinds F.G K F.m F.n F.hs F.r) := by
  intro μ
  have witness := strict_source_missing_heights F paid K
  have kinds := strict_single_unpaid_types F paid K
  exact ⟨fun esc inner => ⟨witness.1 esc,kinds.1 esc inner⟩,fun esc inner => ⟨witness.2 esc,kinds.2 esc inner⟩⟩

#print axioms strict_single_unpaid_types
#print axioms strict_single_escape_winner
end JSP452Audit.StarHost
