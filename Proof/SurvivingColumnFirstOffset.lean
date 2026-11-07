import CompleteOriginalDegreeStages
namespace JSP452Audit.StarHost

theorem width_positive_at_first_offset {s t r j:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) :
    0<widthAt n m r j ↔ 0<rowCount s t r ∧ j≤diagonal n m (r+2) := by
  have range := offsetsAt_eq_range hs ht n m hn hm r j
  have zero : (0:ℕ)∈offsetsAt n m r j ↔ 0<widthAt n m r j := by rw [range,Finset.mem_range]
  rw [←zero]
  change (0:ℕ)∈(Finset.range (rowCount s t r)).filter (fun k => j≤diagonal n m (r+k+2)) ↔ _
  simp

theorem shifted_live_six_has_exact_head {s t r k:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (gone:widthAt n m r 7≤k) (present:k<widthAt n m r 6) :
    0<rowCount s t (r+k) ∧ diagonal n m ((r+k)+2)=6 ∧ highestWidth n m (r+k)=widthAt n m r 6-k := by
  have shift := widthAt_shift hs ht n m hn hm r k
  have live6 : 0<widthAt n m (r+k) 6 := by rw [shift];omega
  have dead7 : widthAt n m (r+k) 7=0 := by rw [shift];omega
  obtain ⟨live,lo⟩ := (width_positive_at_first_offset hs ht n m hn hm).mp live6
  have head : diagonal n m (r+k+2)=6 := by
    by_contra! no
    have hit := (width_positive_at_first_offset (j:=7) hs ht n m hn hm).mpr ⟨live,by omega⟩
    omega
  have eq := width_at_actual_top hs ht n m hn hm (r:=r+k)
  rw [head,shift] at eq
  exact ⟨live,head,eq.symm⟩

#print axioms width_positive_at_first_offset
#print axioms shifted_live_six_has_exact_head
end JSP452Audit.StarHost
