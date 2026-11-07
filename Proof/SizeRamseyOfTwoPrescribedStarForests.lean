import ThePaidCoreAndTheFullExteriorStageCloseEveryOriginalStrictSource
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Size Ramsey number for two prescribed nonempty star forests. Mathematical solution by P. Liu. -/
theorem sizeRamsey_star_forests (s t:ℕ) (hs:1≤s) (ht:1≤t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j) :
    sizeRamsey (forest n) (forest m)=∑j∈Finset.Icc 2 (s+t),diagonal n m j := by
  by_contra fail
  obtain ⟨F,paid,_⟩ := original_failure_has_only_the_first_gap.{0} hs ht n m hn hm pn pm fail
  exact no_original_strict_family F paid

#print axioms sizeRamsey_star_forests
end JSP452Audit.StarHost