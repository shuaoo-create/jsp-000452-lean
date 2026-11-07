import MateBlockSeparation
import OddSmallAlphaMatching
import MateHoleTransport
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem noIndependentTriple_of_set_bound (G : SimpleGraph X)
    (bound : ∀K : Set X,G.IsIndepSet K → K.ncard≤2) : NoIndependentTriple G := by
  classical
  intro x y z xy xz yz
  by_contra! h
  obtain ⟨nxy,nxz,nyz⟩ := h
  have independent : G.IsIndepSet ({x,y,z} : Set X) := by
    intro a ha b hb ne edge
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
      first | exact ne rfl | exact nxy edge | exact nxz edge | exact nyz edge |
              exact nxy edge.symm | exact nxz edge.symm | exact nyz edge.symm
  have size := bound _ independent
  have apart : x∉({y,z} : Set X) := by simp [xy,xz]
  rw [Set.ncard_insert_of_notMem apart,Set.ncard_pair yz] at size
  omega

theorem actual_block_small_alpha (Q : SimpleGraph X) (D : ℕ) (pos : 0<D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (zero : baseReserve Q D=0) (I : Set X) (ind : Q.IsIndepSet I)
    (max : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (v : X) (vi : v∈I) (M : Q.Subgraph) (hm : M.IsMatching) (expose : M.verts={x|x≠v})
    (w : ↥(Iᶜ : Set X)) (hw : w∉(restrictedOutsideMatching Q I M).verts) :
    let H := Q.induce Iᶜ
    let N := restrictedOutsideMatching Q I M
    NoIndependentTriple (H.induce (mateBlock H N w)) := by
  intro H N
  obtain ⟨matchN,rank,labels,count,_⟩ := independent_mate_barrier Q D pos reg crit zero I ind v vi M hm expose
  have gap : N.vertsᶜ.ncard+1=I.ncard := by
    rw [← labels,Set.ncard_image_of_injective _ Subtype.val_injective] at count
    exact count
  exact noIndependentTriple_of_set_bound _ (actual_mateBlock_independent_bound Q I N matchN rank w hw max gap)

#print axioms actual_block_small_alpha
end JSP452Audit.StarHost
