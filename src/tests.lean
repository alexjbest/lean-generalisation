import generalisation_linter
import algebra.associated
import topology.metric_space.basic
import algebra.ring
import algebra.category.Group
import algebra.group_power
import algebra.algebra.basic
import analysis.convex.integral
import measure_theory.set_integral

/-! Tests for generalisation linter, should produce test.expected.out -/
namespace lint_tests
section

  variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

  lemma is_unit.pow [monoid α] {a : α} (n : ℕ) : is_unit a → is_unit (a ^ n) :=
  λ ⟨u, hu⟩, ⟨u ^ n, by simp *⟩

  theorem is_unit_iff_dvd_one [comm_monoid α] {x : α} : is_unit x ↔ x ∣ 1 :=
  ⟨by rintro ⟨u, rfl⟩; exact ⟨_, u.mul_inv.symm⟩,
  λ ⟨y, h⟩, ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

end

section

  lemma atest (α : Type*) [comm_monoid α] : (1 : α) * 1 = 1 ∧ ∀ a b : α, a * b = b * a := ⟨mul_one _, mul_comm⟩
  lemma btest (α : Type*) [ordered_ring α] (a b : α) : (0 : α) ≤ 0 ∧ a * b + b = a * b + b := ⟨eq.le rfl, rfl⟩
  lemma btest' (α : Type*) [has_add α] [has_mul α] [has_zero α] [preorder α] (a b : α) : (0 : α) ≤ 0 ∧ a * b + b = a * b + b := ⟨eq.le rfl, rfl⟩

end
section

  universe u
  variables (α : Type u) [integral_domain α]

  open char_p nat
  theorem char_ne_one (p : ℕ) [hc : char_p α p] : p ≠ 1 :=
  assume hp : p = 1,
  have ( 1 : α) = 0, by simpa using (cast_eq_zero_iff α p 1).mpr (hp ▸ dvd_refl p),
  absurd this one_ne_zero

  theorem char_is_prime_of_two_le (p : ℕ) [hc : char_p α p] (hp : 2 ≤ p) : nat.prime p :=
  suffices ∀d ∣ p, d = 1 ∨ d = p, from ⟨hp, this⟩,
  assume (d : ℕ) (hdvd : ∃ e, p = d * e),
  let ⟨e, hmul⟩ := hdvd in
  have (p : α) = 0, from (cast_eq_zero_iff α p p).mpr (dvd_refl p),
  have (d : α) * e = 0, from (@cast_mul α _ d e) ▸ (hmul ▸ this),
  or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
    (assume hd : (d : α) = 0,
    have p ∣ d, from (cast_eq_zero_iff α p d).mp hd,
    show d = 1 ∨ d = p, from or.inr (dvd_antisymm ⟨e, hmul⟩ this))
    (assume he : (e : α) = 0,
    have p ∣ e, from (cast_eq_zero_iff α p e).mp he,
    have e ∣ p, from dvd_of_mul_left_eq d (eq.symm hmul),
    have e = p, from dvd_antisymm ‹e ∣ p› ‹p ∣ e›,
    have h₀ : p > 0, from gt_of_ge_of_gt hp (nat.zero_lt_succ 1),
    have d * p = 1 * p, by rw ‹e = p› at hmul; rw [one_mul]; exact eq.symm hmul,
    show d = 1 ∨ d = p, from or.inl (eq_of_mul_eq_mul_right h₀ this))

end
section

open measure_theory set filter
open_locale topological_space big_operators

variables {α E : Type*} [measurable_space α] {μ : measure α}
  [normed_group E] [normed_space ℝ E] [complete_space E]
  [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]

private lemma convex.smul_integral_mem_of_measurable
  [finite_measure μ] {s : set E} (hs : convex s) (hsc : is_closed s)
  (hμ : μ ≠ 0) {f : α → E} (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) (hfm : measurable f) :
  (μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s :=
begin
  rcases eq_empty_or_nonempty s with rfl|⟨y₀, h₀⟩, { refine (hμ _).elim, simpa using hfs },
  rw ← hsc.closure_eq at hfs,
  have hc : integrable (λ _, y₀) μ := integrable_const _,
  set F : ℕ → simple_func α E := simple_func.approx_on f hfm s y₀ h₀,
  have : tendsto (λ n, (F n).integral μ) at_top (𝓝 $ ∫ x, f x ∂μ),
  { simp only [simple_func.integral_eq_integral _
      (simple_func.integrable_approx_on hfm hfi h₀ hc _)],
    exact tendsto_integral_of_l1 _ hfi
      (eventually_of_forall $ simple_func.integrable_approx_on hfm hfi h₀ hc)
      (simple_func.tendsto_approx_on_l1_edist hfm h₀ hfs (hfi.sub hc).2) },
  refine hsc.mem_of_tendsto (tendsto_const_nhds.smul this) (eventually_of_forall $ λ n, _),
  have : ∑ y in (F n).range, (μ ((F n) ⁻¹' {y})).to_real = (μ univ).to_real,
    by rw [← (F n).sum_range_measure_preimage_singleton, @ennreal.to_real_sum _ _
      (λ y, μ ((F n) ⁻¹' {y})) (λ _ _, (measure_lt_top _ _))],
  rw [← this, simple_func.integral],
  refine hs.center_mass_mem (λ _ _, ennreal.to_real_nonneg) _ _,
  { rw [this, ennreal.to_real_pos_iff, pos_iff_ne_zero, ne.def, measure.measure_univ_eq_zero],
    exact ⟨hμ, measure_ne_top _ _⟩ },
  { simp only [simple_func.mem_range],
    rintros _ ⟨x, rfl⟩,
    exact simple_func.approx_on_mem hfm h₀ n x }
end

  /-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
  integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
  `(μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem` for a finite sum version
  of this lemma. -/
lemma convex.smul_integral_mem
  [finite_measure μ] {s : set E} (hs : convex s) (hsc : is_closed s)
  (hμ : μ ≠ 0) {f : α → E} (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) :
  (μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s :=
begin
  have : ∀ᵐ (x : α) ∂μ, hfi.ae_measurable.mk f x ∈ s,
  { filter_upwards [hfs, hfi.ae_measurable.ae_eq_mk],
    assume a ha h,
    rwa ← h },
  convert convex.smul_integral_mem_of_measurable hs hsc hμ this
    (hfi.congr hfi.ae_measurable.ae_eq_mk) (hfi.ae_measurable.measurable_mk) using 2,
  apply integral_congr_ae,
  exact hfi.ae_measurable.ae_eq_mk
end

end

section

  variables {α : Type*} [linear_ordered_ring α] [archimedean α]

  lemma pow_unbounded_of_one_lt (x : α) {y : α} (hy1 : 1 < y) :
    ∃ n : ℕ, x < y ^ n :=
  sub_add_cancel y 1 ▸ add_one_pow_unbounded_of_pos _ (sub_pos.2 hy1)

  /-- Every x greater than or equal to 1 is between two successive
  natural-number powers of every y greater than one. -/
  lemma exists_nat_pow_near {x : α} {y : α} (hx : 1 ≤ x) (hy : 1 < y) :
    ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) :=
  have h : ∃ n : ℕ, x < y ^ n, from pow_unbounded_of_one_lt _ hy,
  by classical; exact let n := nat.find h in
    have hn  : x < y ^ n, from nat.find_spec h,
    have hnp : 0 < n,     from pos_iff_ne_zero.2 (λ hn0,
      by rw [hn0, pow_zero] at hn; exact (not_le_of_gt hn hx)),
    have hnsp : nat.pred n + 1 = n,     from nat.succ_pred_eq_of_pos hnp,
    have hltn : nat.pred n < n,         from nat.pred_lt (ne_of_gt hnp),
    ⟨nat.pred n, le_of_not_lt (nat.find_min h hltn), by rwa hnsp⟩

  theorem exists_int_gt (x : α) : ∃ n : ℤ, x < n :=
  let ⟨n, h⟩ := exists_nat_gt x in ⟨n, by rwa ← coe_coe⟩
  --- only needs semiring and has neg doesn't matter what negative ints do.

end

section
  variables {α : Type*} [linear_ordered_ring α] {a b c : α}

  @[simp] lemma mul_le_mul_right_of_neg {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
  ⟨le_imp_le_of_lt_imp_lt $ λ h', mul_lt_mul_of_neg_right h' h,
    λ h', mul_le_mul_of_nonpos_right h' h.le⟩

end

section
  lemma good (G : Type*) [group G] (n : ℤ) (g : G) (h : g^(-n) = 1) : g^n = 1 :=
  begin
    rw [gpow_neg, inv_eq_one] at h,
    exact h,
  end

  lemma good2 (G : Type*) [add_monoid G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- monoid?
  lemma bad (G : Type*) [group G] (n : ℕ) (g : G) (h : g^n = 1) : g^(2*n) = 1 :=
  by rw [pow_mul', h, one_pow]

  -- add_monoid
  lemma bad2diamond (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- statement generalises but proof does not!! this one is hard then, beyond current scope to complete
  -- add_monoid linter only finds semiring
  lemma bad3pfbad (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by simp only [nsmul_eq_mul] at h; simp only [nat.cast_bit0, nsmul_eq_mul, nat.cast_one, nat.cast_mul]; assoc_rewrite h; exact mul_zero 2

  lemma bad3 (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by {rw [mul_nsmul, h], exact nsmul_zero _}

  -- add_monoid
  lemma bad4 (G : Type*) [add_comm_group G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- add_monoid
  lemma bad5 (G : Type*) [add_group G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- add_comm_semigroup
  lemma bad6 (G : Type*) [add_comm_group G] (g h : G) : g + h = h + g := add_comm _ _

  -- add_comm_semigroup
  lemma bad8 (G H : Type*) [add_comm_group G] (g h : G) : g + h = h + g := add_comm _ _

  -- add_comm_semigroup
  lemma bad7pibinder (G : Type*) [add_comm_group G] (g h : G) : g + h = h + g ∧ ∀ g2, g2 + g = g + g2 :=
  ⟨add_comm _ _,assume g2, add_comm _ _ ⟩

  -- this example this is not an instance or even a tc
  lemma bad10 (G H : Type*) [has_mul G] [has_mul H] [fintype G] [fintype H] (h : G ≃* H) :
  fintype.card G = fintype.card H := fintype.card_congr h.to_equiv

  -- multiple tings
  -- monoid H, fintypes not needed
  lemma bad9 (G H : Type*) [monoid G] [group H] [fintype G] [fintype H] : (1^2 : G) = 1 ∧ (1^2 : H) = 1 :=
  ⟨one_pow 2, one_pow 2⟩

  -- group
  lemma bad11 (G : Type*) [comm_group G] (n : ℤ) (g : G) (h : g^(-n) = 1) : g^n = 1 :=
  begin
    rw [gpow_neg, inv_eq_one] at h,
    exact h,
  end

  -- bundled examples do nothing
  lemma bun (G : Group) (g : G) : g^2*g^2 = g^4 :=
  begin
    group,
  end

end

section
  def eval {M N : Type*} [monoid M] [comm_monoid N] : M →* (M →* N) →* N := (monoid_hom.id (M →* N)).flip
end

section
  local attribute [semireducible] int.nonneg
  lemma one_lt_fpow {K} [linear_ordered_field K] {p : K} (hp : 1 < p) :
    ∀ z : ℤ, 0 < z → 1 < p ^ z
  | (int.of_nat n) h := one_lt_pow hp (nat.succ_le_of_lt (int.lt_of_coe_nat_lt_coe_nat h))

end

section

  open equiv.set equiv sum nat function set subtype

  @[simp] lemma sum_diff_subset_apply_inr {α : Sort} {β : Sort} {γ : Sort}
    {α} {s t : set α} (h : s ⊆ t) [decidable_pred s] (x : t \ s) :
    equiv.set.sum_diff_subset h (sum.inr x) = inclusion (diff_subset t s) x := rfl

  lemma supr_apply {α : Type*} {β : α → Type*} {ι : Sort*} [Π i, has_Sup (β i)] {f : ι → Πa, β a}
    {a : α} :
    (⨆i, f i) a = (⨆i, f i a) :=
  @infi_apply α (λ i, order_dual (β i)) _ _ f a

end

section

  variables {α β γ :Type} {ι : Sort} {s : set α}
  --none
  theorem exists_nat_ge [linear_ordered_semiring α] [archimedean α] (x : α) :
    ∃ n : ℕ, x ≤ n :=
  (exists_nat_gt x).imp $ λ n, le_of_lt

  theorem finset_le {r : α → α → Prop} [is_trans α r]
    {ι} [hι : nonempty ι] {f : ι → α} (D : directed r f) (s : finset ι) :
    ∃ z, ∀ i ∈ s, r (f i) (f z) :=
  show ∃ z, ∀ i ∈ s.1, r (f i) (f z), from
  multiset.induction_on s.1 (let ⟨z⟩ := hι in ⟨z, λ _, false.elim⟩) $
  λ i s ⟨j, H⟩, let ⟨k, h₁, h₂⟩ := D i j in
  ⟨k, λ a h, or.cases_on (multiset.mem_cons.1 h)
    (λ h, h.symm ▸ h₁)
    (λ h, trans (H _ h) h₂)⟩
end

section
  variables {α β :Type}
  open set
  lemma finite.bdd_below_bUnion [semilattice_inf α] [nonempty α] {I : set β} {S : β → set α} (H : finite I) :
    (bdd_below (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_below (S i)) :=
  @finite.bdd_above_bUnion (order_dual α) _ _ _ _ _ H
end

section

  open filter set
  variables {α β :Type}
  variables  {ι' : Type}
  lemma unbounded_of_tendsto_at_top [nonempty α] [semilattice_inf α] [preorder β] [no_top_order β]
    {f : α → β} (h : tendsto f at_bot at_top) :
    ¬ bdd_above (range f) :=
  @unbounded_of_tendsto_at_top (order_dual α) _ _ _ _ _ _ h

end

section
  -- it looks like we only need has_pow here as has_pow is all that appears in the proof
  -- however to_monoid and to_inv also appear in the statement, so should not show up
  theorem gpow_neg_succ_of_nat {G : Type } [group G] (a : G) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl
  -- set_option pp.all true
  -- #print gpow_neg_succ_of_nat
end

section
  lemma char_p_iff_char_p {K L : Type*} [field K] [field L] (f : K →+* L) (p : ℕ) :
    char_p K p ↔ char_p L p :=
  begin
    split;
    { introI _c, constructor, intro n,
      rw [← @char_p.cast_eq_zero_iff _ _ p _c n, ← f.injective.eq_iff, f.map_nat_cast, f.map_zero] }
  end

end

section
  open nat subtype multiset
  variables {α β :Type}

  lemma piecewise_piecewise_of_subset_left {δ : α → Sort*} (s : finset α) (g f : Π (i : α), δ i) [Π (j : α), decidable (j ∈ s)] {s t : finset α} [Π i, decidable (i ∈ s)]
    [Π i, decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : Π a, δ a) :
    s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  s.piecewise_congr (λ i hi, finset.piecewise_eq_of_mem _ _ _ (h hi)) (λ _ _, rfl)

end

section
  variables {α β :Type}

  lemma sub_le_of_abs_sub_le_left {c b a : α} [linear_ordered_ring α] (h : abs (a - b) ≤ c) : b - c ≤ a :=
  if hz : 0 ≤ a - b then
    (calc
        a ≥ b     : le_of_sub_nonneg hz
      ... ≥ b - c : sub_le_self _ $ (abs_nonneg _).trans h)
  else
    have habs : b - a ≤ c, by rwa [abs_of_neg (lt_of_not_ge hz), neg_sub] at h,
    have habs' : b ≤ c + a, from sub_le_iff_le_add.mp habs,
    sub_le.mp habs

end

section
  variables {α β :Type}
  lemma inf_ind [semilattice_inf α] [is_total α (≤)] (a b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊓ b) :=
  @sup_ind (order_dual α) _ _ _ _ _ ha hb
end

section
  variables {α β :Type}

  open filter
  open_locale filter
  lemma map_at_bot_eq [nonempty α] [semilattice_inf α] {f : α → β} :
    at_bot.map f = (⨅a, 𝓟 $ f '' {a' | a' ≤ a}) :=
  @map_at_top_eq (order_dual α) _ _ _ _

end

section
  variables {α β : Type}
  open_locale big_operators
  lemma abs_sum_le_sum_abs [linear_ordered_field α] {f : β → α} {s : finset β} :
    abs (∑ x in s, f x) ≤ ∑ x in s, abs (f x) :=
  finset.le_sum_of_subadditive _ abs_zero abs_add s f
end

section
  universes u v w

  lemma mem_orbit_self
  {α : Type u} {β : Type v} [monoid α] [mul_action α β]
  (b : β) : b ∈ mul_action.orbit α b :=
  ⟨1, mul_action.one_smul _⟩
end

section
  variable {R : Type}
  variables [euclidean_domain R]
  variable [decidable_eq R]
  open euclidean_domain

  /-- `gcd a b` is a (non-unique) element such that `gcd a b ∣ a` `gcd a b ∣ b`, and for
    any element `c` such that `c ∣ a` and `c ∣ b`, then `c ∣ gcd a b` -/
  def gcd : R → R → R
  | a := λ b, if a0 : a = 0 then b else
    have h:_ := mod_lt b a0,
    gcd (b%a) a
  using_well_founded {dec_tac := tactic.assumption,
    rel_tac := λ _ _, `[exact ⟨_, r_well_founded⟩]}

end

section
  universes u v w
  open algebra
  variables {R : Type u} {S : Type v} {A : Type w} {B : Type*}

  /-- Let `R` be a commutative semiring, let `A` be a semiring with a `semimodule R` structure.
  If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `algebra`
  over `R`. -/
  def of_semimodule [comm_semiring R] [semiring A] [semimodule R A]
    (h₁ : ∀ (r : R) (x : A), (r • 1) * x = r • x)
    (h₂ : ∀ (r : R) (x : A), x * (r • 1) = r • x) : algebra R A :=
  { to_fun := λ r, r • 1,
    map_one' := one_smul _ _,
    map_mul' := λ r₁ r₂, by rw [h₁, mul_smul],
    map_zero' := zero_smul _ _,
    map_add' := λ r₁ r₂, add_smul r₁ r₂ 1,
    commutes' := λ r x, by simp only [h₁, h₂],
    smul_def' := λ r x, by simp only [h₁] }

end

section
  /- _inst_2: decidable_eq ↝ -/

  open_locale big_operators
  open finset
  variables {α β γ : Type}
  variables [comm_monoid β]
  @[simp, to_additive]
  lemma prod_sum_elim [decidable_eq (α ⊕ γ)]
    (s : finset α) (t : finset γ) (f : α → β) (g : γ → β) :
    ∏ x in s.image sum.inl ∪ t.image sum.inr, sum.elim f g x = (∏ x in s, f x) * (∏ x in t, g x) :=
  begin
    rw [prod_union, prod_image, prod_image],
    { simp only [sum.elim_inl, sum.elim_inr] },
    { exact λ _ _ _ _, sum.inr.inj },
    { exact λ _ _ _ _, sum.inl.inj },
    { rintros i hi,
      erw [finset.mem_inter, finset.mem_image, finset.mem_image] at hi,
      rcases hi with ⟨⟨i, hi, rfl⟩, ⟨j, hj, H⟩⟩,
      cases H }
  end
end
section

  variables {α β : Type} {s s₁ s₂ : finset α} {a : α} {b : β} {f g : α → β} [semiring β]
  open_locale big_operators
  open function

  -- odd one the linter wants to assume add_comm_monoid has_mul and is_add_monoid_hom mul
  -- this is weaker than semiring indeed as no mul identity needed
  lemma sum_mul : (∑ x in s, f x) * b = ∑ x in s, f x * b :=
  (s.sum_hom (λ x, x * b)).symm
end

section
  universes u v
  variables {α : Type u} {β : Type v} [topological_space α]
  lemma is_closed_singleton [t2_space α] {x : α} : is_closed ({x} : set α) :=
  t1_space.t1 x

end

section

class foo (X : Type) :=
(f : X → X)
class bar (X : Type) extends foo X :=
(h : f ∘ f = f)
end

section

lemma aa (X : Type) [bar X] : (foo.f : X → X) = foo.f := rfl

lemma mn_tors_of_n_tors {X : Type*} [semiring X] (m n : ℕ) (x : X) (h : n •ℕ x = 0) :
  (m * n) •ℕ x = 0 := by rw [mul_nsmul, h, nsmul_zero]
end

#lint only generalisation_linter
end lint_tests
