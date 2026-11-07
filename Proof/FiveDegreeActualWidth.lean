import LowDegreeFullHead
import UniformSubforest
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

/-- Exact-width uniform forests, taken together from one actual highest
legal original corner of the same forcing host. -/
theorem original_highest_corner_uniform_width {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r) :
    ∃(i:Fin s) (j:Fin t) (p q:ℕ),i.val+j.val=r ∧ diagonal n m (r+2)=n i+m j-1 ∧
      0<p ∧ 0<q ∧ p≤headWidth n i ∧ q≤headWidth m j ∧ p+q-1=highestWidth n m r ∧
      Forces G (forest (fun _ : Fin p => n i)) (forest (fun _ : Fin q => m j)) := by
  obtain ⟨i,j,index,attain,width⟩ := highest_column_head_pair hs ht n m hn hm pn pm r live
  let h := highestWidth n m r
  have positive : 0<h := Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,by simp⟩⟩
  let p := min h (headWidth n i)
  let q := h+1-p
  have red := headWidth_pos n i
  have blue := headWidth_pos m j
  change h≤headWidth n i+headWidth m j-1 at width
  have ppos : 0<p := lt_min positive red
  have ple : p≤headWidth n i := Nat.min_le_right _ _
  have qpos : 0<q := by dsimp [q,p];omega
  have qle : q≤headWidth m j := by dsimp [q,p];omega
  refine ⟨i,j,p,q,index,attain,ppos,qpos,ple,qle,?_,?_⟩
  · change p+q-1=h;dsimp [q,p];omega
  · exact forces_uniform_subforests G (originalTail n i) (originalTail m j) (n i) (m j) p q ple qle
      (forces_original_tails G n m row i j index)

theorem five_degree_two_subcap_lists_force_four_three (F : StrictFamily.{u})
    (five : diagonal F.n F.m (F.r+2)-1=5) (red : F.n ⟨0,F.hs⟩<5) (blue : F.m ⟨0,F.ht⟩<5) :
    ∃(i:Fin F.s) (j:Fin F.t) (p q:ℕ),i.val+j.val=F.r ∧ 0<p ∧ 0<q ∧
      p≤headWidth F.n i ∧ q≤headWidth F.m j ∧ p+q-1=highestWidth F.n F.m F.r ∧
      ((F.n i=4 ∧ F.m j=3) ∨ (F.n i=3 ∧ F.m j=4)) ∧
      Forces F.G (forest (fun _ : Fin p => F.n i)) (forest (fun _ : Fin q => F.m j)) := by
  obtain ⟨i,j,p,q,idx,att,hp,hq,cp,cq,charge,force⟩ := original_highest_corner_uniform_width
    F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.row F.live
  have ri := F.hn (show (⟨0,F.hs⟩ : Fin F.s)≤ i from Nat.zero_le _)
  have bj := F.hm (show (⟨0,F.ht⟩ : Fin F.t)≤ j from Nat.zero_le _)
  exact ⟨i,j,p,q,idx,hp,hq,cp,cq,charge,by omega,force⟩

/-- Color-normalized 4-versus-3 input, keeping the exact highest-column
width and the true host; the previous theorem preserves the actual corner. -/
theorem five_degree_uniform_obstruction (F : StrictFamily.{u})
    (five : diagonal F.n F.m (F.r+2)-1=5) (red : F.n ⟨0,F.hs⟩<5) (blue : F.m ⟨0,F.ht⟩<5) :
    ∃p q:ℕ,0<p ∧ 0<q ∧ p+q-1=highestWidth F.n F.m F.r ∧
      Forces F.G (forest (fun _ : Fin p => 4)) (forest (fun _ : Fin q => 3)) := by
  obtain ⟨i,j,p,q,_,hp,hq,_,_,charge,split,force⟩ := five_degree_two_subcap_lists_force_four_three F five red blue
  rcases split with ⟨a,b⟩|⟨a,b⟩
  · exact ⟨p,q,hp,hq,charge,by rwa [a,b] at force⟩
  · rw [a,b] at force
    exact ⟨q,p,hq,hp,by simpa [Nat.add_comm q p] using charge,forces_swap force⟩

#print axioms original_highest_corner_uniform_width
#print axioms five_degree_two_subcap_lists_force_four_three
#print axioms five_degree_uniform_obstruction
end JSP452Audit.StarHost
