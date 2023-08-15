/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.Data.Finsupp.WellFounded

/-!
# The Fundamental Theorem of Symmetric Polynomials

In a polynomial ring in n variables over a commutative ring, the subalgebra of symmetric
polynomials is freely generated by the first n elementary symmetric polynomials (excluding
the 0th, which is simply 1). This is expressed as an isomorphism with the symmetric subalgebra
with the polynomials in n variables, `MvPolynomial.equiv_symmetricSubalgebra`.

## Proof strategy

We follow the alternative proof on the Wikipedia page
https://en.wikipedia.org/wiki/Elementary_symmetric_polynomial#Alternative_proof

TODO:
details
declaration docstrings
move ordered monoid instances on `Lex (σ →₀ β)`
move maxDegree API
-/

section OrderedAddMonoidLex

variable (σ : Type*) [LinearOrder σ]

instance (β) [CanonicallyOrderedAddMonoid β] : OrderBot (Lex (σ →₀ β)) where
  bot := 0
  bot_le _ := Finsupp.toLex_monotone bot_le

noncomputable instance (β) [LinearOrderedCancelAddCommMonoid β] :
    LinearOrderedCancelAddCommMonoid (Lex (σ →₀ β)) :=
  { (inferInstance : LinearOrder (Lex (σ →₀ β))) with
    add_le_add_left := fun a b h c => by
      obtain rfl | ⟨i, h⟩ := h.eq_or_lt
      · rfl
      exact le_of_lt ⟨i, fun j hj => congr_arg (ofLex c j + ·) (h.1 j hj), add_lt_add_left h.2 _⟩
    le_of_add_le_add_left := fun a b c h => by
      obtain h | ⟨i, h⟩ := h.eq_or_lt
      · exact (add_left_cancel h).le
      exact le_of_lt ⟨i, fun j hj => (add_left_cancel <| h.1 j hj), lt_of_add_lt_add_left h.2⟩ }

/- TODO:
#check OrderedAddCommMonoid
#check OrderedAddCommGroup
#check LinearOrderedAddCommMonoid
#check LinearOrderedAddCommGroup
#check OrderedCancelAddCommMonoid
#check LinearOrderedCancelAddCommMonoid -/

end OrderedAddMonoidLex

namespace MvPolynomial

open BigOperators Finset

variable {σ τ R : Type*} {n m : ℕ}

section maxDegree

variable [LinearOrder σ] [CommSemiring R] (p q : MvPolynomial σ R)

def maxDegree : Lex (σ →₀ ℕ) := p.support.sup toLex
def leadingCoeff : R := p.coeff (ofLex p.maxDegree)
def Monic : Prop := p.leadingCoeff = 1

lemma maxDegree_C (r : R) : maxDegree (C (σ := σ) r) = 0 := by
  classical
  rw [← monomial_zero', maxDegree, support_monomial]
  split_ifs
  · rw [sup_empty]; rfl
  · rw [sup_singleton]; rfl

lemma leadingCoeff_C (r : R) : leadingCoeff (C (σ := σ) r) = r := by
  rw [leadingCoeff, maxDegree_C, coeff_C]; apply if_pos rfl

lemma maxDegree_zero : maxDegree (0 : MvPolynomial σ R) = 0 := by rw [← C_0, maxDegree_C]

lemma ne_zero_of_maxDegree : p.maxDegree ≠ 0 → p ≠ 0 := mt (fun h => h ▸ maxDegree_zero)

lemma leadingCoeff_zero : leadingCoeff (0 : MvPolynomial σ R) = 0 := by rw [← C_0, leadingCoeff_C]

lemma maxDegree_monomial (t : σ →₀ ℕ) {r : R} (hr : r ≠ 0) :
    maxDegree (monomial t r) = toLex t := by
  classical
  rw [maxDegree, support_monomial, if_neg hr, sup_singleton]

lemma leadingCoeff_monomial (t : σ →₀ ℕ) (r : R) : leadingCoeff (monomial t r) = r := by
  obtain rfl | hr := eq_or_ne r 0
  · rw [monomial_zero, leadingCoeff_zero]
  · rw [leadingCoeff, maxDegree_monomial t hr, coeff_monomial, if_pos]; rfl

lemma monic_one : Monic (1 : MvPolynomial σ R) := leadingCoeff_C 1

variable {p q}

/- May be these lemmas belong to Finset.sup (for linear orders) -/
lemma maxDegree_mem_support (hp : p ≠ 0) : ofLex p.maxDegree ∈ p.support := by
  rw [Ne, ← support_eq_empty, ← Ne, ← nonempty_iff_ne_empty] at hp
  obtain ⟨t, ht, he⟩ := exists_mem_eq_sup _ hp toLex
  rw [maxDegree, he]; exact ht

lemma leadingCoeff_eq_zero : leadingCoeff p = 0 ↔ p = 0 := by
  refine' ⟨(fun h => _).mtr, fun h => h ▸ leadingCoeff_zero⟩
  rw [leadingCoeff, ← Ne, ← mem_support_iff]
  exact maxDegree_mem_support h

lemma maxDegree_eq_of_max {t : Lex (σ →₀ ℕ)} (hmem : ofLex t ∈ p.support)
    (hmax : ∀ s ∈ p.support, toLex s ≤ t) : p.maxDegree = t := by
  apply le_antisymm _ (le_sup hmem)
  apply hmax _ (maxDegree_mem_support _)
  rw [Ne, ← support_eq_empty]
  exact ne_empty_of_mem hmem

lemma le_maxDegree_of_mem_support {t : Lex (σ →₀ ℕ)}
    (ht : ofLex t ∈ p.support) : t ≤ p.maxDegree := Eq.trans_le (by rfl) (le_sup ht)

lemma coeff_eq_zero_of_maxDegree_lt {t : σ →₀ ℕ} (ht : p.maxDegree < toLex t) : p.coeff t = 0 := by
  contrapose! ht; exact le_maxDegree_of_mem_support (mem_support_iff.2 ht)

lemma IsSymmetric.antitone_maxDegree (hp : p.IsSymmetric) : Antitone (ofLex p.maxDegree) := by
  obtain rfl | h0 := eq_or_ne p 0
  · rw [maxDegree_zero]; exact fun _ _ _ => le_rfl
  rw [Antitone]; by_contra h; push_neg at h
  obtain ⟨i, j, hle, hlt⟩ := h
  apply (le_maxDegree_of_mem_support (p := p) (t := toLex _) _).not_lt
  pick_goal 3
  · rw [← hp (Equiv.swap i j), mem_support_iff, ofLex_toLex, coeff_rename_mapDomain]
    · rwa [Ne, ← leadingCoeff_eq_zero] at h0
    · apply Equiv.injective
  refine' ⟨i, fun k hk => _, _⟩
  all_goals dsimp only [Pi.toLex_apply, ofLex_toLex]
  · conv_rhs => rw [← Equiv.swap_apply_of_ne_of_ne hk.ne (hk.trans_le hle).ne]
    rw [Finsupp.mapDomain_apply (Equiv.injective _)]
  · apply hlt.trans_eq
    convert ← (Finsupp.mapDomain_apply (Equiv.injective _) _ _).symm
    exact Equiv.swap_apply_right i j

lemma maxDegree_le_of_support {t : Lex (σ →₀ ℕ)} (ht : ∀ s ∈ p.support, toLex s ≤ t) :
    p.maxDegree ≤ t := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [maxDegree_zero]; exact bot_le
  · exact ht _ (maxDegree_mem_support hp)

lemma maxDegree_le_of_coeff {t : Lex (σ →₀ ℕ)} (ht : ∀ s, t < toLex s → p.coeff s = 0) :
    p.maxDegree ≤ t := maxDegree_le_of_support fun s h => by
  rw [mem_support_iff] at h; contrapose! h; exact ht s h

--lemma maxDegree_lt_of_support {t : Lex (σ →₀ ℕ)} ... 0 < t or p ≠ 0

lemma maxDegree_add_le : (p + q).maxDegree ≤ max p.maxDegree q.maxDegree := by
  refine' maxDegree_le_of_coeff fun s h => _
  rw [max_lt_iff] at h
  rw [coeff_add, coeff_eq_zero_of_maxDegree_lt h.1, coeff_eq_zero_of_maxDegree_lt h.2, add_zero]

lemma maxDegree_sum_le {α} {s : Finset α} (f : α → MvPolynomial σ R) {t}
    (h : ∀ i ∈ s, (f i).maxDegree ≤ t) : (∑ i in s, f i).maxDegree ≤ t := by
  refine' sum_induction f (fun p => maxDegree p ≤ t) _ bot_le h
  intros p q hp hq; exact maxDegree_add_le.trans (max_le_iff.2 ⟨hp, hq⟩)

lemma maxDegree_sum_lt {α} {s : Finset α} (hs : s.Nonempty) (f : α → MvPolynomial σ R) {t}
    (h : ∀ i ∈ s, (f i).maxDegree < t) : (∑ i in s, f i).maxDegree < t := by
  refine' sum_induction f (fun p => maxDegree p < t) _ _ h
  · intros p q hp hq; exact maxDegree_add_le.trans_lt (max_lt_iff.2 ⟨hp, hq⟩)
  · obtain ⟨i, hi⟩ := hs; rw [maxDegree_zero]; exact bot_le.trans_lt (h i hi)

lemma maxDegree_add_eq (h : q.maxDegree < p.maxDegree) :
    (p + q).maxDegree = p.maxDegree := by
  refine' maxDegree_eq_of_max _ (fun s hs => _)
  · rw [mem_support_iff, coeff_add, ← leadingCoeff, coeff_eq_zero_of_maxDegree_lt, add_zero]
    · rw [Ne, leadingCoeff_eq_zero]; rintro rfl; exact not_lt_bot (h.trans_eq maxDegree_zero)
    · exact h
  · rw [mem_support_iff, coeff_add] at hs
    contrapose! hs
    rw [coeff_eq_zero_of_maxDegree_lt hs, coeff_eq_zero_of_maxDegree_lt (h.trans hs), add_zero]

lemma leadingCoeff_add_eq (h : q.maxDegree < p.maxDegree) :
    (p + q).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff, maxDegree_add_eq h, coeff_add, ← leadingCoeff, coeff_eq_zero_of_maxDegree_lt]
  exacts [add_zero _, h]

lemma maxDegree_leadingCoeff_sum_eq {α} (s : Finset α) {a : α} (ha : a ∈ s)
    (f : α → MvPolynomial σ R)
    (h : ∀ i ∈ s, i ≠ a → (f i).maxDegree < (f a).maxDegree) :
    (∑ a in s, f a).maxDegree = (f a).maxDegree ∧
    (∑ a in s, f a).leadingCoeff = (f a).leadingCoeff := by
  classical
  rw [← s.add_sum_erase _ ha]
  by_cases hs : s.erase a = ∅
  · rw [hs, sum_empty, add_zero]; exact ⟨rfl, rfl⟩
  have : _; swap; refine' ⟨maxDegree_add_eq this, leadingCoeff_add_eq this⟩
  refine' maxDegree_sum_lt _ _ <| fun i hi => _
  · rw [nonempty_iff_ne_empty]; exact hs
  · rw [mem_erase] at hi; exact h i hi.2 hi.1

lemma ne_zero_of_injOn' {α} {s : Finset α} (f : α → MvPolynomial σ R) (hs : ∃ a ∈ s, f a ≠ 0)
    (hd : (s : Set α).InjOn (maxDegree ∘ f)) :
    ∑ a in s, f a ≠ 0 := by
  classical
  simp_rw [← mem_filter (p := fun i => f i ≠ 0)] at hs
  obtain ⟨a, ha, he⟩ := exists_mem_eq_sup _ hs (maxDegree ∘ f)
  rw [← sum_filter_ne_zero, Ne, ← leadingCoeff_eq_zero,
      (maxDegree_leadingCoeff_sum_eq _ ha f _).2]
  · rw [leadingCoeff_eq_zero]; exact (mem_filter.1 ha).2
  refine' fun i hi hne => ((le_sup hi).trans_eq he).lt_of_ne (hd.ne _ _ hne)
  exacts [(mem_filter.1 hi).1, (mem_filter.1 ha).1]

lemma ne_zero_of_injOn {α} {s : Finset α} (hs : s ≠ ∅) (f : α → MvPolynomial σ R)
    (hf : ∀ a ∈ s, f a ≠ 0) (hd : (s : Set α).InjOn (maxDegree ∘ f)) :
    ∑ a in s, f a ≠ 0 := by
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 hs
  exact ne_zero_of_injOn' f ⟨a, ha, hf a ha⟩ hd

lemma maxDegree_neg {R} [CommRing R] {p : MvPolynomial σ R} : (-p).maxDegree = p.maxDegree := by
  rw [maxDegree, maxDegree, support_neg]

lemma maxDegree_sub_le {R} [CommRing R] {p q : MvPolynomial σ R} :
    (p - q).maxDegree ≤ max p.maxDegree q.maxDegree := by
  rw [sub_eq_add_neg, ← maxDegree_neg (p := q)]; apply maxDegree_add_le

lemma maxDegree_sub_lt_of_leadingCoeff_eq {R} [CommRing R] {p q : MvPolynomial σ R}
    (hd : p.maxDegree = q.maxDegree) (hc : p.leadingCoeff = q.leadingCoeff) :
    (p - q).maxDegree < p.maxDegree ∨ p = q := by
  by_cases he : p = q; exact Or.inr he
  refine' Or.inl ((maxDegree_sub_le.trans _).lt_of_ne _)
  · rw [hd, max_self]
  · rw [← sub_eq_zero, ← leadingCoeff_eq_zero, leadingCoeff] at he
    refine' fun h => he _
    rwa [h, coeff_sub, ← leadingCoeff, hd, ← leadingCoeff, sub_eq_zero]

lemma coeff_maxDegree_add_maxDegree :
    (p * q).coeff (ofLex (maxDegree p + maxDegree q)) = p.leadingCoeff * q.leadingCoeff := by
  rw [coeff_mul, sum_eq_single_of_mem (ofLex p.maxDegree, ofLex q.maxDegree)]; rfl
  · exact Finsupp.mem_antidiagonal.2 rfl
  · rintro ⟨tp, tq⟩ ht hne
    obtain htp | htp := lt_or_le p.maxDegree (toLex tp)
    · rw [coeff_eq_zero_of_maxDegree_lt htp, zero_mul]
    obtain htq | htq := lt_or_le q.maxDegree (toLex tq)
    · rw [coeff_eq_zero_of_maxDegree_lt htq, mul_zero]
    have := eq_and_eq_of_le_of_le_of_add_le htp htq (Eq.ge <| Finsupp.mem_antidiagonal.1 ht)
    exact (hne <| Prod.ext this.1.symm this.2.symm).elim

lemma Monic.maxDegree_mul' (hq : q.Monic) (hp : p ≠ 0) :
    maxDegree (p * q) = maxDegree p + maxDegree q := by
  apply maxDegree_eq_of_max
  · rwa [mem_support_iff, coeff_maxDegree_add_maxDegree, hq, mul_one, Ne, leadingCoeff_eq_zero]
  · intro s hs
    replace hs := support_mul _ _ hs
    simp_rw [mem_biUnion] at hs
    obtain ⟨tp, htp, tq, htq, he⟩ := hs
    cases mem_singleton.1 he
    exact add_le_add (le_maxDegree_of_mem_support htp) (le_maxDegree_of_mem_support htq)

lemma Monic.maxDegree_mul (hp : p.Monic) (hq : q.Monic) :
    maxDegree (p * q) = maxDegree p + maxDegree q := by
  obtain hs | hn := subsingleton_or_nontrivial R
  · simp only [Subsingleton.eq_zero p, Subsingleton.eq_zero q, add_zero, mul_zero, maxDegree_zero]
  apply hq.maxDegree_mul'; rw [Ne, ← leadingCoeff_eq_zero, hp]; exact one_ne_zero

lemma Monic.leadingCoeff_mul (hq : q.Monic) :
    leadingCoeff (p * q) = leadingCoeff p := by
  obtain rfl | hp := eq_or_ne p 0; rw [zero_mul]
  rw [leadingCoeff, hq.maxDegree_mul' hp, coeff_maxDegree_add_maxDegree, hq, mul_one]

lemma Monic.mul (hp : p.Monic) (hq : q.Monic) : (p * q).Monic := by
  rw [Monic, hq.leadingCoeff_mul]; exact hp

lemma Monic.pow {n} (hp : p.Monic) : Monic (p ^ n) := by
  induction' n with n ih
  · rw [pow_zero]; exact monic_one
  · rw [pow_succ]; exact hp.mul ih

lemma Monic.maxDegree_pow {n} (hp : p.Monic) : maxDegree (p ^ n) = n • maxDegree p := by
  induction' n with n ih
  · rw [pow_zero, zero_nsmul]; exact maxDegree_C 1
  · rw [pow_succ', hp.pow.maxDegree_mul hp, ih, succ_nsmul']

end maxDegree

section accumulate

/-- The `j`th entry of `accumulate m t` is the sum of `t i` over all `i ≤ j`. -/
@[simps] def accumulate (n m : ℕ) : (Fin n → ℕ) →+ (Fin m → ℕ) where
  toFun t j := ∑ i in univ.filter (fun i : Fin n => (j : ℕ) ≤ i), t i
  map_zero' := funext <| fun j => sum_eq_zero <| fun h _ => rfl
  map_add' t₁ t₂ := funext <| fun j => by dsimp only; exact sum_add_distrib

def inv_accumulate (n m : ℕ) (s : Fin m → ℕ) (i : Fin n) : ℕ :=
  (if hi : i < m then s ⟨i, hi⟩ else 0) - (if hi : i + 1 < m then s ⟨i + 1, hi⟩ else 0)

lemma accumulate_rec {i n m : ℕ} (hin : i < n) (him : i + 1 < m) (t : Fin n → ℕ) :
    accumulate n m t ⟨i, i.lt_succ_self.trans him⟩ = t ⟨i, hin⟩ + accumulate n m t ⟨i+1, him⟩ := by
  simp_rw [accumulate_apply]
  convert (add_sum_erase _ _ _).symm
  · ext; rw [mem_erase]
    simp_rw [mem_filter, mem_univ, true_and, i.succ_le_iff, lt_iff_le_and_ne]
    rw [and_comm, ne_comm, ← Fin.val_ne_iff]
  · exact mem_filter.2 ⟨mem_univ _, le_rfl⟩

lemma accumulate_last {i n m : ℕ} (hin : i < n) (hmi : m = i + 1) (t : Fin n → ℕ)
    (ht : ∀ j : Fin n, m ≤ j → t j = 0) :
    accumulate n m t ⟨i, i.lt_succ_self.trans_eq hmi.symm⟩ = t ⟨i, hin⟩ := by
  rw [accumulate_apply]
  apply sum_eq_single_of_mem
  · rw [mem_filter]; exact ⟨mem_univ _, le_rfl⟩
  refine' fun j hij hji => ht j _
  simp_rw [mem_filter, mem_univ, true_and] at hij
  exact hmi.trans_le (hij.lt_of_ne (Fin.val_ne_iff.2 hji).symm).nat_succ_le

lemma injective_accumulate {n m} (hnm : n ≤ m) : Function.Injective (accumulate n m) := by
  refine' fun t s he => funext fun i => _
  obtain h|h := lt_or_le (i.1 + 1) m
  · have := accumulate_rec i.2 h s
    rwa [← he, accumulate_rec i.2 h t, add_right_cancel_iff] at this
  · have := h.antisymm (i.2.nat_succ_le.trans hnm)
    rw [← accumulate_last i.2 this t, ← accumulate_last i.2 this s, he]
    iterate 2 { intro j hj; exact ((j.2.trans_le hnm).not_le hj).elim }

lemma surjective_accumulate {n m} (hmn : m ≤ n) {s : Fin m → ℕ} (hs : Antitone s) :
    accumulate n m (inv_accumulate n m s) = s := funext <| fun ⟨i, hi⟩ => by
  have := Nat.le_pred_of_lt hi
  revert hi
  refine' Nat.decreasingInduction' (fun i hi _ ih => _) this _
  · intro him
    rw [m.sub_one, Nat.lt_pred_iff] at hi
    rw [accumulate_rec (him.trans_le hmn) hi, ih hi, inv_accumulate, dif_pos him, dif_pos hi]
    exact Nat.sub_add_cancel (hs i.le_succ)
  · intro hm
    have := (Nat.succ_pred <| Nat.not_eq_zero_of_lt hm).symm
    rw [accumulate_last (hm.trans_le hmn) this, inv_accumulate, dif_pos hm, dif_neg, Nat.sub_zero]
    · exact this.not_gt
    intro j hj
    rw [inv_accumulate, dif_neg hj.not_lt, Nat.zero_sub]

end accumulate

section CommSemiring

variable (σ R n) [CommSemiring R]

noncomputable def esymmAlgHom [Fintype σ] :
    MvPolynomial (Fin n) R →ₐ[R] symmetricSubalgebra σ R :=
  aeval (fun i => ⟨esymm σ R (i + 1), esymm_isSymmetric σ R _⟩)

variable {σ R n}

lemma esymmAlgHom_apply [Fintype σ] (p : MvPolynomial (Fin n) R) :
    (esymmAlgHom σ R n p).val = aeval (fun i : Fin n => esymm σ R (i + 1)) p :=
  (Subalgebra.mvPolynomial_aeval_coe _ _ _).symm

lemma rename_esymmAlgHom [Fintype σ] [Fintype τ] (e : σ ≃ τ) :
    (rename_symmetricSubalgebra e).toAlgHom.comp (esymmAlgHom σ R n) = esymmAlgHom τ R n := by
  refine' algHom_ext (fun i => Subtype.ext _)
  simp_rw [AlgHom.comp_apply, esymmAlgHom, aeval_X]
  exact rename_esymm σ R _ e

noncomputable def esymmAlgHom_monomial (σ) [Fintype σ] (t : Fin n →₀ ℕ) (r : R) :
    MvPolynomial σ R := (esymmAlgHom σ R n <| monomial t r).val

variable {m k : ℕ} {i : Fin n} {j : Fin m} {r : R} (hr : r ≠ 0)

lemma isSymmetric_esymmAlgHom_monomial [Fintype σ] (t : Fin n →₀ ℕ) (r : R) :
    (esymmAlgHom_monomial σ t r).IsSymmetric := (esymmAlgHom _ _ _ _).2

lemma esymmAlgHom_monomial_single [Fintype σ] :
    esymmAlgHom_monomial σ (Finsupp.single i k) r = C r * esymm σ R (i + 1) ^ k := by
  rw [esymmAlgHom_monomial, esymmAlgHom_apply, aeval_monomial, algebraMap_eq,
      Finsupp.prod_single_index]; apply pow_zero

lemma esymmAlgHom_monomial_single_one [Fintype σ] :
    esymmAlgHom_monomial σ (Finsupp.single i k) 1 = esymm σ R (i + 1) ^ k := by
  rw [esymmAlgHom_monomial_single]; apply one_mul

lemma esymmAlgHom_monomial_add [Fintype σ] {t s : Fin n →₀ ℕ} :
    esymmAlgHom_monomial σ (t + s) r = esymmAlgHom_monomial σ t r * esymmAlgHom_monomial σ s 1 := by
  simp_rw [esymmAlgHom_monomial, esymmAlgHom_apply, ← map_mul, monomial_mul, mul_one]

lemma esymmAlgHom_zero [Fintype σ] : esymmAlgHom_monomial σ (0 : Fin n →₀ ℕ) r = C r := by
  rw [esymmAlgHom_monomial, monomial_zero', esymmAlgHom_apply, aeval_C]; rfl

lemma maxDegree_monic_esymm [Nontrivial R] {i : ℕ} (him : i < m) :
    maxDegree (esymm (Fin m) R (i + 1)) =
      toLex (Finsupp.indicator (Iic ⟨i, him⟩) fun _ _ => 1) ∧
    Monic (esymm (Fin m) R (i + 1)) := by
  have := maxDegree_leadingCoeff_sum_eq (univ.powersetLen (i + 1))
    (a := Iic (⟨i, him⟩ : Fin m)) ?_ (fun s => monomial (∑ j in s, Finsupp.single j 1) (1 : R)) ?_
  · rwa [← esymm_eq_sum_monomial, sum_finsupp_single, maxDegree_monomial _ one_ne_zero,
         leadingCoeff_monomial] at this
  · exact mem_powersetLen.2 ⟨subset_univ _, Fin.card_Iic _⟩
  intro t ht hne
  simp_rw [maxDegree_monomial _ one_ne_zero, sum_finsupp_single]
  rw [Ne, eq_comm, ← subset_iff_eq_of_card_le, not_subset] at hne
  · simp_rw [← mem_sdiff] at hne
    refine' ⟨min' _ hne, let hkm := mem_sdiff.1 (min'_mem _ hne); ⟨fun k hk => _, _⟩⟩
    all_goals simp only [Pi.toLex_apply, ofLex_toLex, Finsupp.indicator_apply]
    · have hki := mem_Iic.2 (hk.le.trans <| mem_Iic.1 hkm.1)
      rw [dif_pos hki, dif_pos]
      exact not_not.1 (fun h => lt_irrefl k <| ((lt_min'_iff _ _).1 hk) _ <| mem_sdiff.2 ⟨hki, h⟩)
    · rw [dif_neg hkm.2, dif_pos hkm.1]; exact Nat.zero_lt_one
  · rw [(mem_powersetLen.1 ht).2, Fin.card_Iic]

lemma maxDegree_esymm [Nontrivial R] (him : i < m) :
    ofLex (maxDegree <| esymm (Fin m) R (i + 1)) = accumulate n m (Finsupp.single i 1) := by
  rw [(maxDegree_monic_esymm him).1, ofLex_toLex]
  ext j; simp_rw [Finsupp.indicator_apply, mem_Iic, accumulate_apply, Finsupp.single_apply,
    sum_ite_eq, mem_filter, mem_univ, true_and]; rfl

lemma monic_esymm {i : ℕ} (him : i ≤ m) : Monic (esymm (Fin m) R i) := by
  cases' i with i; rw [esymm_zero]; exact monic_one
  cases subsingleton_or_nontrivial R
  · rw [Monic]; apply Subsingleton.elim
  · exact (maxDegree_monic_esymm him).2

lemma leadingCoeff_esymmAlgHom_monomial (t : Fin n →₀ ℕ) (hnm : n ≤ m) :
    leadingCoeff (esymmAlgHom_monomial (Fin m) t r) = r := by
  apply t.induction₂
  · rw [esymmAlgHom_zero, leadingCoeff_C]
  intro i _ _ _ _ ih
  rw [esymmAlgHom_monomial_add, esymmAlgHom_monomial_single_one, Monic.leadingCoeff_mul, ih]
  exact (monic_esymm <| i.2.trans_le hnm).pow

lemma maxDegree_esymmAlgHom_monomial (t : Fin n →₀ ℕ) (hnm : n ≤ m) :
    ofLex (esymmAlgHom_monomial (Fin m) t r).maxDegree = accumulate n m t := by
  nontriviality R
  apply t.induction₂
  · simp_rw [esymmAlgHom_zero, maxDegree_C, Finsupp.coe_zero, map_zero]; rfl
  intro i _ _ _ _ ih
  have := i.2.trans_le hnm
  rw [esymmAlgHom_monomial_add, esymmAlgHom_monomial_single_one, Monic.maxDegree_mul', ofLex_add,
      Finsupp.coe_add, ih, Finsupp.coe_add, map_add, Monic.maxDegree_pow, ofLex_smul,
      Finsupp.coe_smul, maxDegree_esymm, ← map_nsmul, ← Finsupp.coe_smul, Finsupp.smul_single,
      nsmul_one]; rfl
  · exact this
  · exact monic_esymm this
  · exact (monic_esymm this).pow
  · rwa [Ne, ← leadingCoeff_eq_zero, leadingCoeff_esymmAlgHom_monomial _ hnm]

/- lemma maxDegree_esymmAlgHom_single (him : i < m) :
    maxDegree (esymmAlgHom_monomial (Fin m) (Finsupp.single i k) r) =
    -- if (j : ℕ) ≤ i then k else 0 :=
    accumulate m (Finsupp.single i k) := by
  rw [esymmAlgHom_monomial_single, Monic.maxDegree_mul, maxDegree_C, zero_add, Monic.maxDegree_pow,
      Finsupp.coe_smul, maxDegree_esymm him, ← map_nsmul, Finsupp.smul_single, nsmul_one]; rfl
  exacts [monic_esymm him, (monic_esymm him).pow] -/

end CommSemiring

section CommRing

variable (R) [Fintype σ] [CommRing R]

-- shortcut instance necessary to avoid timeout
instance {K} [CommRing K] : AddCommMonoid K := inferInstance

/- May also holds for cancellative CommSemiring, not sure. -/
lemma injective_esymmAlgHom_Fin (h : n ≤ m) :
    Function.Injective (esymmAlgHom (Fin m) R n) := by
  rw [injective_iff_map_eq_zero]
  refine' fun p => (fun hp => _).mtr
  rw [p.as_sum, map_sum (esymmAlgHom (Fin m) R n), ← Subalgebra.coe_eq_zero,
      AddSubmonoidClass.coe_finset_sum]
  refine' ne_zero_of_injOn (support_eq_empty.not.2 hp) _ (fun t ht => _) (fun t ht s hs he => _)
  · rw [← esymmAlgHom_monomial, Ne, ← leadingCoeff_eq_zero, leadingCoeff_esymmAlgHom_monomial t h]
    rwa [mem_support_iff] at ht
  refine' FunLike.ext' (injective_accumulate h _)
  dsimp only [Function.comp] at he
  rw [mem_coe, mem_support_iff] at ht hs
  rwa [← esymmAlgHom_monomial, ← esymmAlgHom_monomial, ← ofLex_inj, FunLike.ext'_iff,
       maxDegree_esymmAlgHom_monomial ht t h, maxDegree_esymmAlgHom_monomial hs s h] at he

lemma injective_esymmAlgHom (hn : n ≤ Fintype.card σ) :
    Function.Injective (esymmAlgHom σ R n) := by
  rw [← rename_esymmAlgHom (Fintype.equivFin σ).symm, AlgHom.coe_comp]
  exact (AlgEquiv.injective _).comp (injective_esymmAlgHom_Fin R hn)

lemma bijective_esymmAlgHom_Fin (n : ℕ) :
    Function.Bijective (esymmAlgHom (Fin n) R n) := by
  refine' ⟨injective_esymmAlgHom_Fin R le_rfl, _⟩
  rintro ⟨p, hp⟩; rw [← AlgHom.mem_range]
  obtain rfl | h0 := eq_or_ne p 0; apply Subalgebra.zero_mem
  induction' he : p.maxDegree using WellFoundedLT.induction with t ih generalizing p; subst he
  let t := Finsupp.equivFunOnFinite.symm (inv_accumulate n n <| ofLex p.maxDegree)
  have hd : (esymmAlgHom_monomial _ t p.leadingCoeff).maxDegree = p.maxDegree
  · rw [← ofLex_inj, FunLike.ext'_iff, maxDegree_esymmAlgHom_monomial _ _ le_rfl]
    · exact surjective_accumulate le_rfl hp.antitone_maxDegree
    · rwa [Ne, leadingCoeff_eq_zero]
  obtain he | hne := eq_or_ne p (esymmAlgHom_monomial _ t p.leadingCoeff)
  · convert AlgHom.mem_range_self _ (monomial t p.leadingCoeff); exact he
  have := (maxDegree_sub_lt_of_leadingCoeff_eq hd.symm ?_).resolve_right hne
  · specialize ih _ this _ (Subalgebra.sub_mem _ hp <| isSymmetric_esymmAlgHom_monomial _ _) _ rfl
    · rwa [sub_ne_zero]
    convert ← Subalgebra.add_mem _ ih ⟨monomial t p.leadingCoeff, rfl⟩
    apply sub_add_cancel p
  · rw [leadingCoeff_esymmAlgHom_monomial t le_rfl]

lemma surjective_esymmAlgHom_Fin (h : m ≤ n) :
    Function.Surjective (esymmAlgHom (Fin m) R n) := fun p => by
  obtain ⟨q, rfl⟩ := (bijective_esymmAlgHom_Fin R m).2 p
  rw [← AlgHom.mem_range]
  apply q.induction_on
  · intro r; rw [← algebraMap_eq, AlgHom.commutes]; apply Subalgebra.algebraMap_mem
  · intro p q hp hq; rw [map_add]; exact Subalgebra.add_mem _ hp hq
  · intro p i hp; rw [map_mul]; apply Subalgebra.mul_mem _ hp
    rw [AlgHom.mem_range]
    refine' ⟨X ⟨i, i.2.trans_le h⟩, _⟩
    simp_rw [esymmAlgHom, aeval_X]

lemma surjective_esymmAlgHom (hn : Fintype.card σ ≤ n) :
    Function.Surjective (esymmAlgHom σ R n) := by
  rw [← rename_esymmAlgHom (Fintype.equivFin σ).symm, AlgHom.coe_comp]
  exact (AlgEquiv.surjective _).comp (surjective_esymmAlgHom_Fin R hn)

noncomputable def equiv_symmetricSubalgebra (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) R ≃ₐ[R] symmetricSubalgebra σ R :=
  AlgEquiv.ofBijective (esymmAlgHom σ R n)
    ⟨injective_esymmAlgHom R hn.ge, surjective_esymmAlgHom R hn.le⟩

example (hn : Fintype.card σ = n) {p} :
    equiv_symmetricSubalgebra R hn p =
      aeval (fun i => ⟨esymm σ R (i + 1), esymm_isSymmetric _ _ _⟩) p := rfl

end CommRing

end MvPolynomial
