import InsideClique

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Original vertices outside W adjacent to none of W. This definition
contains no assumed mate map or replacement matching. -/
def mateAntineighborhood {X : Type*} (G : SimpleGraph X) (W : Set X) : Set X :=
  {x | x∉W ∧ ∀ w∈W, ¬G.Adj x w}

private theorem ma_independent_insert {X : Type*} (G : SimpleGraph X) (W : Set X)
    (independent : G.IsIndepSet W) (x : X) (away : ∀w∈W,¬G.Adj x w) :
    G.IsIndepSet (insert x W) := by
  rintro a (rfl|ha) b (rfl|hb) distinct edge
  · exact distinct rfl
  · exact away b hb edge
  · exact away a ha edge.symm
  · exact independent ha hb distinct edge

/-- A common antineighborhood outside an independent set of size alpha-1
is a clique: two nonadjacent outside vertices would give alpha+1 actual
distinct independent vertices. -/
theorem mate_antineighborhood_clique {X : Type*} [Finite X] (G : SimpleGraph X)
    (I W : Set X) (_indI : G.IsIndepSet I)
    (maximum : ∀ S : Set X, G.IsIndepSet S → S.ncard≤I.ncard)
    (indW : G.IsIndepSet W) (gap : W.ncard+1=I.ncard) :
    G.IsClique (mateAntineighborhood G W) := by
  classical
  intro x hx y hy distinct
  by_contra notAdjacent
  have first : G.IsIndepSet (insert x W) := ma_independent_insert G W indW x hx.2
  have second : G.IsIndepSet (insert y (insert x W)) := by
    apply ma_independent_insert G (insert x W) first y
    rintro w (rfl|hw)
    · exact fun edge => notAdjacent edge.symm
    · exact hy.2 w hw
  have yOutside : y∉insert x W := by simp [distinct.symm,hy.1]
  have cap := maximum (insert y (insert x W)) second
  rw [Set.ncard_insert_of_notMem yOutside,Set.ncard_insert_of_notMem hx.1] at cap
  omega

/-- The paper's narrower set, excluding the original maximum independent
set as well, is a genuine subset of the same original-label clique. -/
theorem mate_antineighborhood_excluding_I_clique {X : Type*} [Finite X]
    (G : SimpleGraph X) (I W : Set X) (indI : G.IsIndepSet I)
    (maximum : ∀ S : Set X, G.IsIndepSet S → S.ncard≤I.ncard)
    (indW : G.IsIndepSet W) (gap : W.ncard+1=I.ncard) :
    G.IsClique {x | x∉I ∧ x∉W ∧ ∀w∈W,¬G.Adj x w} :=
  IsClique.subset (fun _ hx => hx.2)
    (mate_antineighborhood_clique G I W indI maximum indW gap)

/-- Whenever an antineighborhood vertex exists, adding that specified
original vertex extends W to a maximum independent set. Existence of such
a vertex is deliberately not asserted. -/
theorem mate_antineighborhood_insert_maximum {X : Type*} [Finite X]
    (G : SimpleGraph X) (I W : Set X)
    (maximum : ∀ S : Set X, G.IsIndepSet S → S.ncard≤I.ncard)
    (indW : G.IsIndepSet W) (gap : W.ncard+1=I.ncard)
    (x : X) (member : x∈mateAntineighborhood G W) :
    G.IsIndepSet (insert x W) ∧ (insert x W).ncard=I.ncard ∧
      ∀ S : Set X, G.IsIndepSet S → S.ncard≤(insert x W).ncard := by
  have size : (insert x W).ncard=I.ncard := by
    rw [Set.ncard_insert_of_notMem member.1,gap]
  exact ⟨ma_independent_insert G W indW x member.2,size,fun S h => size.symm ▸ maximum S h⟩

#print axioms mate_antineighborhood_clique
#print axioms mate_antineighborhood_excluding_I_clique
#print axioms mate_antineighborhood_insert_maximum
end JSP452Audit.StarHost

