import Imo.Basic
import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace IMO2014Q1
variable (a : ℕ → ℕ)             -- define sequence of nonnegative integers
variable (hmono : StrictMono a)  -- define strictly increasing sequence
variable (hpos : ∀ n, a n > 0)   -- define positive integers

-- Define b (shifted by 1)
def b (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n , (a (n+1) - a (k+1))

-- Show that b_0 = 0.
lemma b_zero : b a 0 = 0 := by
  unfold b
  simp

-- Show that (a_n) is increasing.
lemma a_mono {a : ℕ → ℕ}
  (hmono : StrictMono a) {m n : ℕ} (hmn : m ≤ n) : a m ≤ a n := by
    have hmon : Monotone a := hmono.monotone
    exact hmon hmn

-- Show that b is strictly increasing
include hmono
lemma b_strictMono : StrictMono (b a) := by
    intro n m hnm
    unfold b
    have hnm' := Nat.add_lt_add_right hnm 1
    have ineq : a (n+1) < a (m+1) := hmono hnm'
    have hle: ∀ k ∈ Finset.range n, a (n+1) - a (k+1) <= a (m+1) - a (k+1) := by
        intro k hk
        apply Nat.sub_le_sub_right
        apply Nat.le_of_lt
        exact ineq
    have hlt : n > 0 → ∃ i ∈ Finset.range n, a (n+1) - a (i+1) < a (m+1) - a (i+1) := by
        intro hpos
        apply Exists.intro 0
        simp
        apply And.intro
        · exact hpos
        · have : 1 ≤ n + 1 := Nat.le_of_lt (Nat.add_lt_add_right hpos 1)
          have := a_mono hmono this
          exact Nat.sub_lt_sub_right this ineq
    have h1 : n > 0 → ∑ i ∈ Finset.range n, (a (n+1) - a (i+1)) <
        ∑ i ∈ Finset.range n, (a (m+1) - a (i+1)) := by
        intro hpos
        apply Finset.sum_lt_sum hle (hlt hpos)
    have h : Finset.range n ⊆ Finset.range m := Finset.range_subset_range.mpr (Nat.le_of_lt hnm)
    have hpos :
    ∀ j ∈ Finset.range m, j ∉ Finset.range n → 0 ≤ a (m+1) - a (j+1) := by
        intro j hjm hjn
        have hj : j ∈ Finset.range m \ Finset.range n :=
            by apply Finset.mem_sdiff.mpr (And.intro hjm hjn)
        rcases Finset.mem_sdiff.mp hj with ⟨hj_lt_m, hj_ge_n1⟩
        have : a j ≤ a m := a_mono hmono (Nat.le_of_lt (Finset.mem_range.mp hjm))
        grind
    have h' := Finset.sum_le_sum_of_subset_of_nonneg h hpos
    have h1' : n > 0 → 1 + ∑ i ∈ Finset.range n,
    (a (n+1) - a (i+1)) ≤ ∑ i ∈ Finset.range n, (a (m+1) - a (i+1))
    := by
        intro hp
        have hin := Nat.add_le_add_left (Nat.le_sub_one_of_lt (h1 hp)) 1
        grind
    have h2: n > 0 → ∑ k ∈ Finset.range n, (a (n+1) - a (k+1))
    < ∑ k ∈ Finset.range m, (a (m+1) - a (k+1)) :=
     by
        intro hp
        have :=  Nat.lt_add_one_iff.mpr (Nat.le_trans (h1' hp) h')
        have h2'' := Nat.sub_le_sub_right this 1
        grind
    have : n = 0 ∨ n > 0 := by grind
    cases this with
    | inr hp => exact h2 hp
    | inl zero =>
        simp [zero]
        simp [zero] at hnm
        have hle1 : ∀ k ∈ Finset.range m, 0 ≤ a (m + 1) - a (k + 1) := by
            intro k hk
            have := Finset.mem_range.mp hk
            have := Nat.add_lt_add_right this 1
            have := Nat.le_of_lt this
            have := a_mono hmono this
            grind
        have hlt1 : ∃ i ∈ Finset.range m, 0 < a (m + 1) - a (i + 1) := by
            apply Exists.intro 0
            simp
            apply And.intro
            · exact hnm
            · exact hmono (Nat.add_lt_add_right hnm 1)
        have hf:= Finset.sum_lt_sum hle1 hlt1
        grind

-- Show the equivalence condition of the inequality for (a_n) and (b_n)
lemma a_b_equiv_cond (n : ℕ) :
  ((a (n+1) : ℝ) < (∑ k ∈ Finset.range (n+2), a k) / (n+1)) ∧
     ((∑ k ∈ Finset.range (n+2), a k) / (n+1) ≤ (a (n+2) : ℝ))
  ↔ (b a n < a 0 ∧ a 0 ≤ b a (n+1)) := by
  have hsum : ∑ k ∈ Finset.range (n+1), a k
      = (n: ℝ) * a (n+1) - b a n + a 0 := by
    apply Eq.symm
    calc (n: ℝ) * a (n+1) - b a n + a 0
        _= n * a (n+1) - ∑ k ∈ Finset.range n, (a (n+1) - a (k+1)) + a 0 := by simp [b]
        _= n * a (n+1) - ∑ k ∈ Finset.range n, ((a (n+1) : ℝ) - (a (k+1) : ℝ)) + a 0 := by
             rw [Nat.cast_sum]
             congr 1
             congr 1
             apply Finset.sum_congr rfl
             intro k hk
             rw [Nat.cast_sub]
             apply a_mono hmono
             apply Nat.succ_le_succ_iff.mpr
             apply Nat.le_of_lt
             apply Finset.mem_range.mp hk
        _= n * a (n+1) - (∑ k ∈ Finset.range n, (a (n+1) : ℝ)
                - ∑ k ∈ Finset.range n, (a (k+1) : ℝ)) + a 0 := by
             rw [Finset.sum_sub_distrib]
        _= n * a (n+1) - (n * a (n+1) - ∑ k ∈ Finset.range n, (a (k+1) : ℝ)) + a 0 := by
             simp
        _= ∑ k ∈ Finset.range n, a (k+1) + a 0 := by
            ring_nf
            simp
            grind
        _= ∑ k ∈ Finset.range (n+1), a k := by
             rw [Finset.sum_range_succ']
             ring_nf
             simp
  have hsum' : ∑ k ∈ Finset.range (n+2), a k
      = (n+1 : ℝ) * a (n+1) - b a n + a 0 := by
      apply Eq.symm
      calc (n + 1 : ℝ) * a (n+1) - b a n + a 0
        _= ((n : ℝ) * a (n+1) + a (n+1)) - b a n + a 0 := by ring
        _= ((n : ℝ) * a (n+1) - b a n + a 0) + a (n+1) := by ring_nf
        _= ∑ k ∈ Finset.range (n+1), a k + a (n+1) := by rw [hsum]
        _=∑ k ∈ Finset.range (n+2), a k := by
            apply Eq.symm
            rw [Finset.sum_range_succ]
            grind
  have h_b_rec : b a (n+1) = b a n + (n+1) * (a (n+2) - a (n+1)) := by
    simp [b]
    rw [Finset.sum_range_succ]

    have split_sum : ∑ x ∈ Finset.range n, (a (n + 2) - a (x + 1)) =
                     ∑ x ∈ Finset.range n, ((a (n + 1) - a (x + 1)) + (a (n + 2) - a (n + 1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [add_comm (a (n + 1) - a (k + 1)) (a (n+2) - a (n + 1))]
        rw [Nat.sub_add_sub_cancel]
        · apply a_mono hmono
          apply Nat.le_succ
        · apply a_mono hmono
          apply Nat.le_of_lt
          apply Nat.add_one_lt_add_one_iff.mpr
          exact Finset.mem_range.mp hk
    rw [split_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    ring
  have hsum_div :  (∑ k ∈ Finset.range (n+2), a k) / (n+1)
      = ((n + 1: ℝ) * a (n+1) - b a n + a 0) / (n+1) := by rw [hsum']
  constructor
  · intro h
    rcases h with ⟨h₁, h₂⟩
    rw [hsum_div] at h₁
    rw [hsum_div] at h₂
    constructor
    · rw [lt_div_iff₀ (Nat.cast_add_one_pos n)] at h₁
      rw [mul_comm (a (n + 1) : ℝ) (n + 1 : ℝ)] at h₁
      rw [sub_add_eq_add_sub, lt_sub_iff_add_lt, add_lt_add_iff_left] at h₁
      norm_cast at h₁
    · rw [h_b_rec]
      rw [← Nat.cast_le (α := ℝ)]
      rw [div_le_iff₀ (Nat.cast_add_one_pos n)] at h₂
      rw [sub_add_eq_add_sub, sub_le_iff_le_add] at h₂
      rw [add_comm _ (b a n : ℝ), add_comm ((n+1 : ℝ) * a (n+1))] at h₂
      rw [← le_sub_iff_add_le] at h₂
      rw [add_sub_assoc] at h₂
      simp
      rw [Nat.cast_sub (a_mono hmono (Nat.le_succ _))]
      rw [mul_sub]
      grind
  · intro h
    rcases h with ⟨h₁, h₂⟩
    constructor
    · rw [hsum']
      rw [lt_div_iff₀ (Nat.cast_add_one_pos n)]
      rw [mul_comm (a (n + 1) : ℝ) (n + 1 : ℝ)]
      apply lt_add_of_sub_left_lt
      simp
      exact h₁
    · rw [hsum']
      rw [div_le_iff₀ (Nat.cast_add_one_pos n), mul_comm (a (n + 2) : ℝ) (n + 1 : ℝ)]
      rw [sub_add_eq_add_sub, sub_le_iff_le_add]
      rw [← Nat.cast_le (α := ℝ)] at h₂
      rw [h_b_rec, Nat.cast_add, Nat.cast_mul] at h₂
      rw [Nat.cast_sub (a_mono hmono (Nat.le_succ _)), mul_sub] at h₂
      simp at h₂
      grind

-- Show the unique existence of n satisfying the inequality for (b_n)
lemma exists_unique_n :
  ∃! n, b a n < a 0 ∧ a 0 ≤ b a (n+1) := by sorry

theorem imo_problem :
  ∃! n,
    (a n : ℝ) < (∑ k ∈ Finset.range (n+1), a k) / n ∧
    (∑ k ∈ Finset.range (n+1), a k) / n ≤ (a (n+1) : ℝ) := by

    obtain ⟨n, hn_all, huniq⟩ := exists_unique_n a hmono
    refine ⟨n + 1, ?prop_n, ?uniq_n⟩
    · simp
      constructor
      · have := ((a_b_equiv_cond a hmono n).mpr hn_all).left
        rw [Nat.cast_sum] at this
        exact this
      · have := ((a_b_equiv_cond a hmono n).mpr hn_all).right
        rw [Nat.cast_sum] at this
        exact this
    · intro m hm_all
      have m_pos : 0 < m := by
          by_contra h; simp at h
          rcases hm_all with ⟨h_lt, _⟩
          rw [h] at *
          simp at h_lt
          norm_cast at h_lt

      let k := m - 1
      have mk : m = k + 1 := (Nat.sub_add_cancel m_pos).symm
      have h_b_k : b a k < a 0 ∧ a 0 ≤ b a (k+1) := by
          rw [mk] at hm_all
          have : k + 1 + 1 = k + 2 := by rfl
          simp [this] at hm_all
          rw [← Nat.cast_sum] at hm_all
          have := (a_b_equiv_cond a hmono k).mp hm_all
          exact this

      have k_is_n : k = n := huniq k h_b_k
      rw [mk, k_is_n]


end IMO2014Q1
