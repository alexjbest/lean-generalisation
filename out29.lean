/- Checking 57012 declarations (plus 54043 automatically generated ones) in mathlib (only in imported files) -/
import all


/- The `generalisation_linter` linter reports: -/
/- typeclass generalisations may be possible: -/
-- algebra\add_torsor.lean
#print vadd_eq_add /- _inst_1: add_group ↝ has_add has_vadd
 -/
#print vsub_eq_sub /- _inst_1: add_group ↝ has_sub has_vsub
 -/
#print vadd_comm /- _inst_1: add_comm_monoid ↝ add_monoid add_comm_semigroup has_vadd
 -/
#print set.has_vsub /- T: add_torsor ↝ has_vsub
 -/
#print vsub_sub_vsub_cancel_left /- _inst_1: add_comm_group ↝ has_vsub add_comm_semigroup add_group
 -/

-- algebra\algebra\basic.lean
#print algebra.of_semimodule' /- _inst_3: semimodule ↝
 -/
#print algebra.of_semimodule /- _inst_3: semimodule ↝
 -/
#print algebra.bit0_smul_one /- _inst_4: algebra ↝
 -/
#print algebra.bit0_smul_bit0 /- _inst_4: algebra ↝
 -/
#print algebra.bit0_smul_bit1 /- _inst_4: algebra ↝
 -/
#print algebra.bit1_smul_bit1 /- _inst_4: algebra ↝
 -/
#print algebra.id.smul_eq_mul /- _inst_1: comm_semiring ↝ has_mul
 -/
#print algebra.mem_algebra_map_submonoid_of_mem /- _inst_2: comm_semiring ↝ semiring
 -/
#print algebra.mul_sub_algebra_map_commutes /- _inst_1: comm_ring ↝ comm_semiring
 -/
#print module.endomorphism_algebra /- _inst_3: semimodule ↝
 -/
#print module.algebra_map_End_eq_smul_id /- _inst_3: semimodule ↝ algebra
 -/
#print module.algebra_map_End_apply /- _inst_3: semimodule ↝ algebra
 -/
#print module.ker_algebra_map_End /- _inst_6: vector_space ↝ algebra
 -/
#print matrix_algebra /- _inst_1: decidable_eq ↝
 -/
#print alg_hom.map_inv /- _inst_1: comm_ring ↝ comm_semiring
 -/
#print alg_hom.map_div /- _inst_1: comm_ring ↝ comm_semiring
 -/
#print alg_equiv.map_neg /- _inst_1: comm_ring ↝ comm_semiring
 -/
#print alg_equiv.map_sub /- _inst_1: comm_ring ↝ comm_semiring
 -/
#print matrix.alg_hom_map_one /- _inst_7: decidable_eq ↝
 -/
#print matrix.alg_equiv_map_one /- _inst_7: decidable_eq ↝
 -/
#print algebra.linear_map.semimodule' /- _inst_6: semimodule ↝
 -/
#print span_nat_eq_add_group_closure /- _inst_1: semiring ↝ add_comm_monoid
 -/
#print span_int_eq_add_group_closure /- _inst_1: ring ↝ add_comm_group
 -/
#print algebra_compatible_smul /- _inst_5: semimodule ↝
_inst_6: semimodule ↝ has_scalar
_inst_7: is_scalar_tower ↝
 -/
#print algebra_map_smul /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print is_scalar_tower.to_smul_comm_class /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print is_scalar_tower.to_smul_comm_class' /- _inst_3: algebra ↝
_inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print smul_algebra_smul_comm /- _inst_3: algebra ↝
_inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print linear_map.coe_is_scalar_tower /- _inst_3: algebra ↝ has_scalar
_inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: is_scalar_tower ↝
 -/
#print linear_map.coe_restrict_scalars_eq_coe /- _inst_3: algebra ↝ has_scalar
_inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: is_scalar_tower ↝
 -/
#print linear_map.coe_coe_is_scalar_tower /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: is_scalar_tower ↝
 -/
#print linear_map.lto_fun /- _inst_14: semimodule ↝
 -/
#print restrict_scalars.module_orig /- I: semimodule ↝
 -/
#print restrict_scalars.semimodule /- _inst_5: semimodule ↝
 -/
#print restrict_scalars_smul_def /- _inst_5: semimodule ↝
 -/
#print restrict_scalars.is_scalar_tower /- _inst_5: semimodule ↝
 -/
#print submodule.restricted_module /- _inst_5: semimodule ↝
 -/
#print submodule.restricted_module_is_scalar_tower /- _inst_5: semimodule ↝
 -/
#print submodule.restrict_scalars_carrier /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print submodule.restrict_scalars /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print submodule.restrict_scalars_mem /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print submodule.restrict_scalars_injective /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print submodule.restrict_scalars_inj /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print submodule.restrict_scalars_bot /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print submodule.restrict_scalars_top /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print linear_map.ker_restrict_scalars /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: is_scalar_tower ↝
 -/
#print linear_map.is_scalar_tower_extend_scalars /- _inst_3: algebra ↝
_inst_5: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: is_scalar_tower ↝
 -/
#print linear_map.smul_algebra_right /- _inst_5: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: is_scalar_tower ↝
 -/
#print linear_map.smul_algebra_right_apply /- _inst_5: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: is_scalar_tower ↝
 -/

-- algebra\algebra\operations.lean
#print submodule.mul_mem_mul_rev /- _inst_2: comm_semiring ↝ comm_semigroup semiring
 -/
#print submodule.map_div /- _inst_4: comm_ring ↝ comm_semiring
 -/

-- algebra\algebra\subalgebra.lean
#print subalgebra.neg_mem /- _inst_6: comm_ring ↝ ring comm_semiring
_inst_7: ring ↝ semiring add_comm_group
 -/
#print subalgebra.ring /- _inst_6: comm_ring ↝ is_subring comm_semiring
 -/
#print subalgebra.to_submodule.is_subring /- _inst_6: comm_ring ↝ is_subring comm_semiring
 -/
#print algebra.bijective_algebra_map_iff /- _inst_6: field ↝ division_ring comm_semiring
 -/

-- algebra\archimedean.lean
#print pow_unbounded_of_one_lt /- _inst_1: linear_ordered_ring ↝ ordered_add_comm_group linear_ordered_semiring
 -/
#print exists_int_gt /- _inst_1: linear_ordered_ring ↝ has_neg linear_ordered_semiring
 -/
#print sub_floor_div_mul_nonneg /- _inst_1: linear_ordered_field ↝ group_with_zero linear_ordered_ring
 -/
#print sub_floor_div_mul_lt /- _inst_1: linear_ordered_field ↝ group_with_zero linear_ordered_ring
 -/
#print exists_rat_gt /- _inst_1: linear_ordered_field ↝ division_ring linear_ordered_semiring
 -/
#print exists_rat_lt /- _inst_1: linear_ordered_field ↝ linear_ordered_ring division_ring
 -/
#print round /- _inst_1: linear_ordered_field ↝ linear_ordered_ring has_div
 -/

-- algebra\associated.lean
#print is_unit_iff_dvd_one /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print dvd_and_not_dvd_iff /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_monoid_with_zero
 -/
#print pow_dvd_pow_iff /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_monoid
 -/
#print prime /- _inst_1: comm_monoid_with_zero ↝ monoid has_zero
 -/
#print left_dvd_or_dvd_right_of_dvd_prime_mul /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_monoid_with_zero
 -/
#print not_irreducible_zero /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print irreducible_of_prime /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_monoid_with_zero
 -/
#print succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_monoid_with_zero
 -/
#print associated_zero_iff_eq_zero /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print associated_mul_mul /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print dvd_iff_dvd_of_rel_left /- _inst_1: comm_monoid_with_zero ↝ monoid
 -/
#print dvd_iff_dvd_of_rel_right /- _inst_1: comm_monoid_with_zero ↝ monoid
 -/
#print eq_zero_iff_of_associated /- _inst_1: comm_monoid_with_zero ↝ monoid mul_zero_class
 -/
#print irreducible_of_associated /- _inst_1: comm_monoid_with_zero ↝ monoid
 -/
#print associated_mul_left_cancel /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_semigroup
 -/
#print associates.mk_one /- _inst_1: comm_monoid ↝ monoid
 -/
#print associates.rel_associated_iff_map_eq_map /- _inst_1: comm_monoid ↝ monoid
 -/
#print associates.mk_eq_zero /- _inst_1: comm_monoid_with_zero ↝ monoid_with_zero
 -/
#print associates.nontrivial /- _inst_1: comm_monoid_with_zero ↝ monoid_with_zero
 -/
#print associates.exists_non_zero_rep /- _inst_1: comm_monoid_with_zero ↝ monoid has_zero
 -/
#print associates.dvd_of_mk_le_mk /- _inst_1: comm_monoid_with_zero ↝ comm_monoid
 -/
#print associates.mk_le_mk_of_dvd /- _inst_1: comm_monoid_with_zero ↝ comm_monoid
 -/
#print associates.no_zero_divisors /- _inst_1: comm_cancel_monoid_with_zero ↝ monoid_with_zero comm_monoid no_zero_divisors
 -/
#print associates.irreducible_iff_prime_iff /- _inst_1: comm_cancel_monoid_with_zero ↝ comm_monoid_with_zero
 -/
#print associates.eq_of_mul_eq_mul_left /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_monoid_with_zero
 -/

-- algebra\big_operators\basic.lean
#print ring_hom.map_multiset_prod /- _inst_1: comm_semiring ↝ comm_monoid semiring
_inst_2: comm_semiring ↝ comm_monoid semiring
 -/
#print ring_hom.map_prod /- _inst_1: comm_semiring ↝ comm_monoid semiring
_inst_2: comm_semiring ↝ comm_monoid semiring
 -/
#print finset.sum_insert /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_insert /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_insert_of_eq_one_if_not_mem /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_insert_of_eq_zero_if_not_mem /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_insert_one /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_insert_zero /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_pair /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_pair /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_image /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_image /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_union_inter /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_union_inter /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_union /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_union /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_sdiff /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_sdiff /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_sum_elim /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_sum_elim /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_bind /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_bind /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_fiberwise_of_maps_to /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_fiberwise_of_maps_to /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_image' /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_image' /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_extend_by_one /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_extend_by_zero /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_dite_eq /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_dite_eq /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_dite_eq' /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_dite_eq' /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_ite_eq /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_ite_eq /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_ite_eq' /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_ite_eq' /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_subset_one_on_sdiff /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_subset_zero_on_sdiff /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_multiset_map_count /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_multiset_count /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_comp /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_piecewise /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_piecewise /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_inter_add_sum_diff /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_inter_mul_prod_diff /- _inst_2: decidable_eq ↝
 -/
#print finset.mul_prod_diff_singleton /- _inst_2: decidable_eq ↝
 -/
#print finset.add_sum_diff_singleton /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_cancels_of_partition_cancels /- _inst_2: decidable_rel ↝
 -/
#print finset.prod_cancels_of_partition_cancels /- _inst_2: decidable_rel ↝
 -/
#print finset.sum_update_of_not_mem /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_update_of_not_mem /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_update_of_mem /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_erase /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_erase /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_pow_boole /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_add_prod_eq /- _inst_1: comm_semiring ↝ comm_monoid distrib
 -/
#print finset.sum_update_of_mem /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_comp /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_inv_distrib /- _inst_1: comm_group ↝ has_inv is_group_hom comm_monoid
 -/
#print finset.sum_neg_distrib /- _inst_1: add_comm_group ↝ add_comm_monoid has_neg is_add_group_hom
 -/
#print finset.card_bind /- _inst_1: decidable_eq ↝
 -/
#print finset.card_bind_le /- _inst_1: decidable_eq ↝
 -/
#print finset.card_eq_sum_card_fiberwise /- _inst_1: decidable_eq ↝
 -/
#print finset.card_eq_sum_card_image /- _inst_1: decidable_eq ↝
 -/
#print finset.gsmul_sum /- _inst_1: add_comm_group ↝ add_comm_monoid add_group
 -/
#print finset.prod_eq_zero /- _inst_1: comm_monoid_with_zero ↝ comm_monoid mul_zero_class
 -/
#print finset.prod_eq_zero_iff /- _inst_1: comm_monoid_with_zero ↝ monoid_with_zero comm_monoid
 -/
#print finset.prod_inv_distrib' /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_monoid_with_zero
 -/
#print list.prod_to_finset /- _inst_1: decidable_eq ↝
 -/
#print list.sum_to_finset /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_sum_count_eq /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_sum' /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_sum_count_smul_eq /- _inst_1: decidable_eq ↝
 -/
#print multiset.exists_smul_of_dvd_count /- _inst_1: decidable_eq ↝
 -/
#print int.coe_prod /- _inst_1: comm_ring ↝ ring comm_semiring
 -/

-- algebra\big_operators\finsupp.lean
#print finsupp.sum_apply' /- _inst_1: add_comm_monoid ↝ has_zero
 -/

-- algebra\big_operators\intervals.lean
#print finset.sum_Ico_eq_add_neg /- _inst_2: add_comm_group ↝ add_comm_monoid add_group
 -/
#print finset.prod_Ico_eq_mul_inv /- _inst_2: comm_group ↝ group comm_monoid
 -/

-- algebra\big_operators\order.lean
#print finset.abs_sum_le_sum_abs /- _inst_1: linear_ordered_field ↝ linear_ordered_add_comm_group
 -/
#print finset.abs_prod /- _inst_1: linear_ordered_comm_ring ↝ comm_monoid linear_ordered_ring
 -/
#print finset.card_le_mul_card_image_of_maps_to /- _inst_2: decidable_eq ↝
 -/
#print finset.card_le_mul_card_image /- _inst_2: decidable_eq ↝
 -/
#print finset.mul_card_image_le_card_of_maps_to /- _inst_2: decidable_eq ↝
 -/
#print finset.mul_card_image_le_card /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_lt_sum_of_subset /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_lt_of_sum_lt /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid linear_order
 -/
#print finset.exists_le_of_sum_le /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ linear_order ordered_cancel_add_comm_monoid
 -/
#print finset.exists_pos_of_sum_zero_of_exists_nonzero /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ linear_order ordered_cancel_add_comm_monoid
 -/
#print finset.prod_nonneg /- _inst_1: linear_ordered_comm_ring ↝ comm_monoid ordered_semiring
 -/
#print finset.prod_pos /- _inst_1: linear_ordered_comm_ring ↝ nontrivial comm_monoid ordered_semiring
 -/

-- algebra\big_operators\pi.lean
#print finset.univ_sum_single /- _inst_1: decidable_eq ↝
 -/
#print add_monoid_hom.functions_ext /- _inst_1: decidable_eq ↝
 -/
#print ring_hom.functions_ext /- _inst_1: decidable_eq ↝
 -/

-- algebra\big_operators\ring.lean
#print finset.sum_mul /- _inst_1: semiring ↝ add_comm_monoid has_mul
 -/
#print finset.mul_sum /- _inst_1: semiring ↝ add_comm_monoid has_mul
 -/
#print finset.sum_mul_boole /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_boole_mul /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_div /- _inst_1: division_ring ↝ group_with_zero semiring
 -/
#print finset.prod_sum /- _inst_1: comm_semiring ↝ comm_monoid semiring
_inst_2: decidable_eq ↝
 -/
#print finset.sum_mul_sum /- _inst_1: comm_semiring ↝ semiring
 -/
#print finset.prod_pow_eq_pow_sum /- _inst_1: comm_semiring ↝ comm_monoid
 -/
#print finset.prod_powerset_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.sum_powerset_insert /- _inst_1: decidable_eq ↝
 -/

-- algebra\category\Algebra\basic.lean
#print Algebra.id_apply /- _inst_1: comm_ring ↝ ring
 -/
#print Algebra.coe_comp /- _inst_1: comm_ring ↝ ring
 -/

-- algebra\category\Group\biproducts.lean
#print AddCommGroup.category_theory.limits.has_biproduct /- _inst_1: decidable_eq ↝
 -/
#print AddCommGroup.biproduct_iso_pi /- _inst_1: decidable_eq ↝
 -/

-- algebra\category\Module\basic.lean
#print Module.has_coe /- _inst_3: module ↝
 -/

-- algebra\char_p.lean
#print char_p.cast_card_eq_zero /- _inst_1: ring ↝ add_group semiring
 -/
#print char_p.int_cast_eq_zero_iff /- _inst_1: ring ↝ add_group semiring
 -/
#print add_pow_char_of_commute /- _inst_1: ring ↝ semiring add_left_cancel_semigroup
 -/
#print add_pow_char /- _inst_1: comm_ring ↝ comm_semigroup ring
 -/
#print add_pow_char_pow /- _inst_1: comm_ring ↝ comm_semigroup ring
 -/
#print sub_pow_char /- _inst_1: comm_ring ↝ comm_semigroup ring
 -/
#print sub_pow_char_pow /- _inst_1: comm_ring ↝ comm_semigroup ring
 -/
#print char_p.neg_one_ne_one /- _inst_1: ring ↝ add_group semiring
 -/
#print ring_hom.char_p_iff_char_p /- _inst_1: field ↝ division_ring
_inst_2: field ↝ nontrivial semiring
 -/
#print frobenius_inj /- _inst_1: integral_domain ↝ comm_ring no_zero_divisors
 -/
#print char_p.char_p_to_char_zero /- _inst_1: ring ↝ add_left_cancel_monoid semiring
 -/
#print char_p.cast_eq_mod /- _inst_1: ring ↝ semiring
 -/
#print char_p.char_ne_one /- _inst_1: integral_domain ↝ nontrivial semiring
 -/
#print char_p.char_is_prime_of_two_le /- _inst_1: integral_domain ↝ no_zero_divisors semiring
 -/
#print char_p.false_of_nontrivial_of_char_one /- _inst_3: char_p ↝ subsingleton
 -/
#print char_p_of_ne_zero /- _inst_1: comm_ring ↝ ring
 -/
#print char_p_of_prime_pow_injective /- _inst_1: comm_ring ↝ ring
 -/

-- algebra\char_zero.lean
#print char_zero_of_inj_zero /- _inst_1: add_left_cancel_monoid ↝ add_monoid add_left_cancel_semigroup
 -/
#print half_add_self /- _inst_1: division_ring ↝ group_with_zero semiring
 -/

-- algebra\continued_fractions\basic.lean
#print generalized_continued_fraction.seq.coe_to_seq /- _inst_1: has_coe ↝ has_lift_t
 -/
#print generalized_continued_fraction.next_numerator /- _inst_1: division_ring ↝ has_add has_mul
 -/
#print generalized_continued_fraction.next_denominator /- _inst_1: division_ring ↝ has_add has_mul
 -/

-- algebra\continued_fractions\computation\basic.lean
#print generalized_continued_fraction.int_fract_pair.of /- _inst_1: linear_ordered_field ↝ linear_ordered_ring
 -/

-- algebra\continued_fractions\computation\correctness_terminating.lean
#print generalized_continued_fraction.comp_exact_value /- _inst_1: linear_ordered_field ↝ linear_order division_ring
 -/
#print generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some_aux_comp /- _inst_1: linear_ordered_field ↝ field linear_ordered_ring
 -/

-- algebra\direct_limit.lean
#print module.direct_limit /- dec_ι: decidable_eq ↝
_inst_2: directed_order ↝ has_le
 -/
#print module.direct_limit.add_comm_group /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.semimodule /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.inhabited /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.of /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.of_f /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.exists_of /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.induction_on /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.lift /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.lift_of /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.lift_unique /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.totalize /- _inst_2: directed_order ↝ has_le
 -/
#print module.direct_limit.to_module_totalize_of_le /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.of.zero_exact_aux /- dec_ι: decidable_eq ↝
 -/
#print module.direct_limit.of.zero_exact /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit.add_comm_group /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit.inhabited /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit.of /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit.of_f /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit.induction_on /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit.of.zero_exact /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit.lift /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit.lift_of /- dec_ι: decidable_eq ↝
 -/
#print add_comm_group.direct_limit.lift_unique /- dec_ι: decidable_eq ↝
 -/
#print ring.direct_limit /- _inst_2: directed_order ↝ has_le
 -/

-- algebra\direct_sum.lean
#print direct_sum.mk /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.of /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.mk_injective /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.of_injective /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.induction_on /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.to_add_monoid /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.to_add_monoid_of /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.to_add_monoid.unique /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.set_to_set /- dec_ι: decidable_eq ↝
 -/

-- algebra\divisibility.lean
#print monoid_has_dvd /- _inst_1: monoid ↝ has_mul
 -/
#print dvd.intro /- _inst_1: monoid ↝ has_dvd has_mul
 -/
#print exists_eq_mul_right_of_dvd /- _inst_1: monoid ↝ has_dvd has_mul
 -/
#print dvd.elim /- _inst_1: monoid ↝ has_dvd has_mul
 -/
#print dvd_trans /- _inst_1: monoid ↝ semigroup has_dvd
 -/
#print dvd.intro_left /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print exists_eq_mul_left_of_dvd /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print dvd_mul_left /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print dvd_mul_of_dvd_right /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print dvd_of_mul_left_dvd /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print eq_zero_of_zero_dvd /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print dvd_zero /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print mul_dvd_mul_iff_right /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_semigroup
 -/
#print units.dvd_mul_left /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print units.mul_left_dvd /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print dvd_not_unit /- _inst_1: comm_monoid_with_zero ↝ monoid has_zero
 -/

-- algebra\euclidean_domain.lean
#print euclidean_domain.gcd /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_zero_left /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_zero_right /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_val /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_dvd /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_dvd_left /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_dvd_right /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_eq_zero_iff /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.dvd_gcd /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_eq_left /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_one_left /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_self /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.xgcd_aux /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.xgcd_zero_left /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.xgcd_aux_rec /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.xgcd /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_a /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_b /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.xgcd_aux_fst /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.xgcd_aux_val /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.xgcd_val /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.xgcd_aux_P /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_eq_gcd_ab /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.lcm /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.dvd_lcm_left /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.dvd_lcm_right /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.lcm_dvd /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.lcm_dvd_iff /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.lcm_zero_left /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.lcm_zero_right /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.lcm_eq_zero_iff /- _inst_2: decidable_eq ↝
 -/
#print euclidean_domain.gcd_mul_lcm /- _inst_2: decidable_eq ↝
 -/

-- algebra\field.lean
#print division_ring_has_div /- _inst_1: division_ring ↝ has_inv has_mul
 -/
#print inverse_eq_has_inv /- _inst_1: division_ring ↝ group_with_zero ring
 -/
#print inv_eq_one_div /- _inst_1: division_ring ↝ group_with_zero
 -/
#print mul_div_assoc' /- _inst_1: division_ring ↝ group_with_zero
 -/
#print one_div_neg_one_eq_neg_one /- _inst_1: division_ring ↝ group_with_zero ring
 -/
#print neg_div /- _inst_1: division_ring ↝ group_with_zero ring
 -/
#print div_add_div_same /- _inst_1: division_ring ↝ has_inv distrib has_div
 -/
#print one_div_mul_add_mul_one_div_eq_one_div_add_one_div /- _inst_1: division_ring ↝ group_with_zero add_comm_semigroup distrib
 -/
#print one_div_mul_sub_mul_one_div_eq_one_div_add_one_div /- _inst_1: division_ring ↝ group_with_zero ring
 -/
#print add_div_eq_mul_add_div /- _inst_1: division_ring ↝ group_with_zero distrib
 -/
#print one_div_add_one_div /- _inst_1: field ↝ add_comm_semigroup distrib comm_group_with_zero
 -/
#print div_add_div /- _inst_1: field ↝ division_ring comm_group_with_zero
 -/
#print ring_hom.map_units_inv /- _inst_2: division_ring ↝ group_with_zero semiring
 -/
#print ring_hom.map_ne_zero /- _inst_1: division_ring ↝ group_with_zero semiring
 -/
#print ring_hom.map_eq_zero /- _inst_1: division_ring ↝ group_with_zero semiring
 -/
#print ring_hom.map_inv /- _inst_1: division_ring ↝ group_with_zero semiring
_inst_4: division_ring ↝ group_with_zero semiring
 -/
#print ring_hom.map_div /- _inst_1: division_ring ↝ group_with_zero semiring
_inst_4: division_ring ↝ group_with_zero semiring
 -/

-- algebra\field_power.lean
#print ring_hom.map_fpow /- _inst_1: division_ring ↝ group_with_zero semiring
_inst_2: division_ring ↝ group_with_zero semiring
 -/
#print neg_fpow_bit0 /- _inst_1: division_ring ↝ group_with_zero ring
 -/
#print neg_fpow_bit1 /- _inst_1: division_ring ↝ group_with_zero ring
 -/
#print one_lt_fpow /- _inst_1: linear_ordered_field ↝ linear_ordered_semiring
 -/
#print rat.cast_fpow /- _inst_1: field ↝ division_ring
 -/

-- algebra\floor.lean
#print abs_sub_lt_one_of_floor_eq_floor /- _inst_3: linear_ordered_comm_ring ↝ linear_ordered_ring comm_ring
 -/

-- algebra\free.lean
#print free_semigroup.traverse /- _inst_1: applicative ↝ has_seq functor
 -/
#print free_add_semigroup.traverse /- _inst_1: applicative ↝ has_seq functor
 -/
#print free_semigroup.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print free_add_semigroup.decidable_eq /- _inst_1: decidable_eq ↝
 -/

-- algebra\gcd_monoid.lean
#print comm_group_with_zero.normalization_monoid /- _inst_1: decidable_eq ↝
 -/
#print comm_group_with_zero.coe_norm_unit /- _inst_1: decidable_eq ↝ normalization_monoid
_inst_2: comm_group_with_zero ↝ group_with_zero comm_cancel_monoid_with_zero
 -/
#print units_eq_one /- _inst_1: comm_cancel_monoid_with_zero ↝ monoid
 -/
#print norm_unit_eq_one /- _inst_2: unique ↝ normalization_monoid
 -/
#print normalize_eq /- _inst_2: unique ↝ normalization_monoid
 -/
#print gcd_eq_of_dvd_sub_right /- _inst_1: integral_domain ↝ comm_cancel_monoid_with_zero nontrivial ring
 -/
#print normalization_monoid_of_monoid_hom_right_inverse /- _inst_3: decidable_eq ↝
 -/
#print gcd_monoid_of_gcd /- _inst_4: decidable_eq ↝
 -/
#print gcd_monoid_of_lcm /- _inst_4: decidable_eq ↝
 -/
#print gcd_monoid_of_exists_gcd /- _inst_4: decidable_eq ↝
 -/
#print gcd_monoid_of_exists_lcm /- _inst_4: decidable_eq ↝
 -/

-- algebra\geom_sum.lean
#print geom_series /- _inst_1: semiring ↝ add_comm_monoid has_pow
 -/
#print op_geom_series /- _inst_1: ring ↝ semiring
 -/
#print geom_series₂ /- _inst_1: semiring ↝ add_comm_monoid has_mul has_pow
 -/
#print geom_series₂_self /- _inst_1: comm_ring ↝ semiring
 -/
#print geom_sum₂_mul_add /- _inst_1: comm_semiring ↝ comm_semigroup semiring
 -/
#print geom_sum₂_mul /- _inst_1: comm_ring ↝ comm_semigroup ring
 -/
#print geom_sum /- _inst_1: division_ring ↝ group_with_zero ring
 -/

-- algebra\group\basic.lean
#print neg_unique /- _inst_1: add_comm_monoid ↝ add_monoid add_comm_semigroup
 -/
#print inv_unique /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print eq_zero_of_add_self_left_cancel /- _inst_1: add_left_cancel_monoid ↝ add_monoid add_left_cancel_semigroup
 -/
#print eq_one_of_mul_self_left_cancel /- _inst_1: left_cancel_monoid ↝ left_cancel_semigroup monoid
 -/
#print eq_one_of_left_cancel_mul_self /- _inst_1: left_cancel_monoid ↝ left_cancel_semigroup monoid
 -/
#print eq_zero_of_left_cancel_add_self /- _inst_1: add_left_cancel_monoid ↝ add_monoid add_left_cancel_semigroup
 -/
#print eq_one_of_mul_self_right_cancel /- _inst_1: right_cancel_monoid ↝ right_cancel_semigroup monoid
 -/
#print eq_zero_of_add_self_right_cancel /- _inst_1: add_right_cancel_monoid ↝ add_monoid add_right_cancel_semigroup
 -/
#print eq_zero_of_right_cancel_add_self /- _inst_1: add_right_cancel_monoid ↝ add_monoid add_right_cancel_semigroup
 -/
#print eq_one_of_right_cancel_mul_self /- _inst_1: right_cancel_monoid ↝ right_cancel_semigroup monoid
 -/
#print add_self_iff_eq_zero /- _inst_1: add_group ↝ add_monoid add_left_cancel_semigroup
 -/
#print mul_self_iff_eq_one /- _inst_1: group ↝ left_cancel_semigroup monoid
 -/
#print mul_left_eq_self /- _inst_1: group ↝ right_cancel_semigroup monoid
 -/
#print add_left_eq_self /- _inst_1: add_group ↝ add_monoid add_right_cancel_semigroup
 -/
#print mul_right_eq_self /- _inst_1: group ↝ left_cancel_semigroup monoid
 -/
#print add_right_eq_self /- _inst_1: add_group ↝ add_monoid add_left_cancel_semigroup
 -/
#print zero_sub /- _inst_1: add_group ↝ has_sub add_monoid has_neg
 -/
#print sub_left_inj /- _inst_1: add_group ↝ has_sub add_right_cancel_semigroup has_neg
 -/
#print neg_add /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print mul_inv /- _inst_1: comm_group ↝ comm_semigroup group
 -/
#print sub_add_eq_sub_sub /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print neg_add_eq_sub /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_add_eq_add_sub /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_sub /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_add /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print add_sub_add_left_eq_sub /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print eq_sub_of_add_eq' /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_eq_of_eq_add' /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print eq_add_of_sub_eq' /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print add_eq_of_eq_sub' /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_sub_self /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print add_sub_comm /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_eq_sub_add_sub /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print neg_neg_sub_neg /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_eq_neg_add /- _inst_1: add_comm_group ↝ has_sub add_comm_semigroup has_neg
 -/
#print eq_sub_iff_add_eq' /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_eq_iff_eq_add' /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_right_comm /- _inst_1: add_comm_group ↝ has_sub add_comm_semigroup has_neg
 -/
#print sub_add_add_cancel /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_add_sub_cancel' /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print sub_sub_sub_cancel_left /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/

-- algebra\group\commute.lean
#print add_neg_cancel_comm /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print mul_inv_cancel_comm /- _inst_1: comm_group ↝ comm_semigroup group
 -/
#print add_neg_cancel_comm_assoc /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print mul_inv_cancel_comm_assoc /- _inst_1: comm_group ↝ comm_semigroup group
 -/
#print neg_add_cancel_comm /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print inv_mul_cancel_comm /- _inst_1: comm_group ↝ comm_semigroup group
 -/
#print inv_mul_cancel_comm_assoc /- _inst_1: comm_group ↝ comm_semigroup group
 -/
#print neg_add_cancel_comm_assoc /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/

-- algebra\group\conj.lean
#print is_conj /- _inst_1: group ↝ has_inv has_mul
 -/
#print is_conj_iff_eq /- _inst_3: comm_group ↝ comm_semigroup group
 -/

-- algebra\group\defs.lean
#print algebra.sub /- _inst_1: add_group ↝ has_neg has_add
 -/
#print sub_eq_add_neg /- _inst_1: add_group ↝ has_sub has_neg has_add
 -/

-- algebra\group\pi.lean
#print add_monoid_hom.single /- _inst_1: decidable_eq ↝
 -/
#print add_monoid_hom.single_apply /- _inst_1: decidable_eq ↝
 -/

-- algebra\group\semiconj.lean
#print add_semiconj_by.add_right /- _inst_1: add_semigroup ↝ has_add is_associative
 -/
#print semiconj_by.mul_right /- _inst_1: semigroup ↝ is_associative has_mul
 -/

-- algebra\group\units.lean
#print units.decidable_eq /- _inst_2: decidable_eq ↝
 -/
#print add_units.decidable_eq /- _inst_2: decidable_eq ↝
 -/
#print divp_eq_divp_iff /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print divp_mul_divp /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/

-- algebra\group_action_hom.lean
#print mul_action_hom.has_coe_to_fun /- _inst_2: mul_action ↝
_inst_3: mul_action ↝
 -/
#print mul_action_hom.map_smul /- _inst_2: mul_action ↝
_inst_3: mul_action ↝
 -/
#print mul_action_hom.ext /- _inst_2: mul_action ↝
_inst_3: mul_action ↝
 -/
#print mul_action_hom.ext_iff /- _inst_2: mul_action ↝
_inst_3: mul_action ↝
 -/
#print mul_action_hom.id /- _inst_2: mul_action ↝
 -/
#print mul_action_hom.id_apply /- _inst_2: mul_action ↝
 -/
#print mul_action_hom.comp /- _inst_2: mul_action ↝
_inst_3: mul_action ↝
_inst_4: mul_action ↝
 -/
#print mul_action_hom.comp_apply /- _inst_2: mul_action ↝
_inst_3: mul_action ↝
_inst_4: mul_action ↝
 -/
#print mul_action_hom.id_comp /- _inst_2: mul_action ↝
_inst_3: mul_action ↝
 -/
#print mul_action_hom.comp_id /- _inst_2: mul_action ↝
_inst_3: mul_action ↝
 -/
#print distrib_mul_action_hom.to_add_monoid_hom /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.to_mul_action_hom /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.has_coe /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.has_coe' /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.has_coe_to_fun /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.coe_fn_coe /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.coe_fn_coe' /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.ext /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.ext_iff /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.map_zero /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.map_add /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.map_neg /- _inst_8: distrib_mul_action ↝
_inst_12: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.map_sub /- _inst_8: distrib_mul_action ↝
_inst_12: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.map_smul /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.id /- _inst_6: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.id_apply /- _inst_6: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.comp /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
_inst_14: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.comp_apply /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
_inst_14: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.id_comp /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/
#print distrib_mul_action_hom.comp_id /- _inst_6: distrib_mul_action ↝
_inst_10: distrib_mul_action ↝
 -/

-- algebra\group_power\basic.lean
#print monoid.has_pow /- _inst_1: monoid ↝ has_one has_mul
 -/
#print monoid.pow_eq_has_pow /- _inst_1: monoid ↝ has_one has_mul has_pow
 -/
#print pow_zero /- _inst_1: monoid ↝ has_one has_pow
 -/
#print zero_nsmul /- _inst_3: add_monoid ↝ has_zero has_add
 -/
#print pow_succ /- _inst_1: monoid ↝ has_mul has_pow
 -/
#print succ_nsmul /- _inst_3: add_monoid ↝ has_zero has_add
 -/
#print pow_ite /- _inst_1: monoid ↝ has_pow
 -/
#print ite_pow /- _inst_1: monoid ↝ has_pow
 -/
#print mul_pow /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print dvd_pow /- _inst_1: comm_monoid ↝ monoid
 -/
#print gpow_coe_nat /- _inst_1: group ↝ has_pow
 -/
#print gpow_of_nat /- _inst_1: group ↝ has_pow
 -/
#print gpow_neg_succ_of_nat /- _inst_1: group ↝ has_inv has_pow
 -/
#print gpow_zero /- _inst_1: group ↝ has_one has_pow
 -/
#print gpow_one /- _inst_1: group ↝ monoid
 -/
#print gpow_neg_one /- _inst_1: group ↝ has_inv monoid
 -/
#print mul_gpow /- _inst_1: comm_group ↝ comm_semigroup group
 -/
#print zero_pow /- _inst_1: monoid_with_zero ↝ has_one mul_zero_class has_pow
 -/
#print pow_two_sub_pow_two /- _inst_1: comm_ring ↝ comm_semigroup ring
 -/
#print eq_or_eq_neg_of_pow_two_eq_pow_two /- _inst_1: integral_domain ↝ comm_ring no_zero_divisors
 -/
#print pow_eq_zero /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print pow_abs /- _inst_1: linear_ordered_comm_ring ↝ linear_ordered_ring
 -/
#print gsmul_nonneg /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/

-- algebra\group_power\lemmas.lean
#print gsmul_pos /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print gsmul_le_gsmul_iff /- _inst_1: linear_ordered_add_comm_group ↝ ordered_add_comm_group
 -/
#print gsmul_lt_gsmul_iff /- _inst_1: linear_ordered_add_comm_group ↝ ordered_add_comm_group
 -/
#print nsmul_le_nsmul_iff /- _inst_1: linear_ordered_add_comm_group ↝ ordered_cancel_add_comm_monoid
 -/
#print nsmul_lt_nsmul_iff /- _inst_1: linear_ordered_add_comm_group ↝ ordered_cancel_add_comm_monoid
 -/
#print nsmul_eq_mul' /- _inst_1: semiring ↝ add_monoid monoid distrib mul_zero_class
 -/
#print bit0_mul /- _inst_1: ring ↝ distrib add_group
 -/
#print mul_bit0 /- _inst_1: ring ↝ distrib add_group
 -/

-- algebra\group_ring_action.lean
#print distrib_mul_action.to_add_monoid_hom /- _inst_7: distrib_mul_action ↝
 -/
#print distrib_mul_action.to_add_equiv /- _inst_7: distrib_mul_action ↝
 -/
#print distrib_mul_action.hom_add_monoid_hom /- _inst_7: distrib_mul_action ↝
 -/
#print multiset.smul_prod /- _inst_5: comm_semiring ↝ comm_monoid semiring
 -/
#print smul_prod /- _inst_5: comm_semiring ↝ comm_monoid semiring
 -/
#print smul_inv /- _inst_6: field ↝ division_ring
 -/

-- algebra\group_with_zero\basic.lean
#print zero_ne_one /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print group_with_zero.has_div /- _inst_1: group_with_zero ↝ has_inv has_mul
 -/
#print units.mul_left_eq_zero /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print units.mul_right_eq_zero /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print eq_zero_of_zero_eq_one /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print div_eq_mul_inv /- _inst_1: group_with_zero ↝ has_inv has_mul has_div
 -/
#print one_div /- _inst_1: group_with_zero ↝ has_inv monoid has_div
 -/
#print zero_div /- _inst_1: group_with_zero ↝ has_inv mul_zero_class has_div
 -/
#print mul_div_assoc /- _inst_1: group_with_zero ↝ semigroup has_inv has_div
 -/
#print mul_inv' /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print one_div_mul_one_div /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print div_mul_right /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print mul_div_cancel_left_of_imp /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print mul_div_cancel_of_imp' /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print mul_div_cancel' /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print mul_div_mul_left /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print div_mul_eq_mul_div /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print div_div_eq_mul_div /- _inst_1: comm_group_with_zero ↝ group_with_zero
 -/
#print ne_zero_of_one_div_ne_zero /- _inst_1: comm_group_with_zero ↝ group_with_zero
 -/
#print eq_zero_of_one_div_eq_zero /- _inst_1: comm_group_with_zero ↝ group_with_zero
 -/
#print div_eq_inv_mul /- _inst_1: comm_group_with_zero ↝ has_inv comm_semigroup has_div
 -/
#print mul_div_right_comm /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print mul_div_comm /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print div_mul_div_cancel /- _inst_1: comm_group_with_zero ↝ group_with_zero
 -/
#print div_eq_div_iff /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/

-- algebra\group_with_zero\power.lean
#print zero_pow' /- _inst_1: monoid_with_zero ↝ has_one mul_zero_class has_pow
 -/
#print pow_eq_zero' /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print fpow_coe_nat /- _inst_1: group_with_zero ↝ has_pow
 -/
#print fpow_of_nat /- _inst_1: group_with_zero ↝ has_pow
 -/
#print fpow_neg_succ_of_nat /- _inst_1: group_with_zero ↝ has_inv has_pow
 -/
#print fpow_zero /- _inst_1: group_with_zero ↝ has_one has_pow
 -/
#print fpow_one /- _inst_1: group_with_zero ↝ monoid
 -/
#print fpow_neg_one /- _inst_1: group_with_zero ↝ has_inv monoid
 -/
#print mul_fpow /- _inst_2: comm_group_with_zero ↝ group_with_zero comm_semigroup
 -/
#print div_pow /- _inst_1: comm_group_with_zero ↝ group_with_zero comm_monoid
 -/

-- algebra\homology\exact.lean
#print category_theory.kernel_comp_cokernel /- _inst_5: category_theory.limits.has_cokernels ↝ category_theory.limits.has_cokernel
 -/

-- algebra\homology\image_to_kernel_map.lean
#print category_theory.image_to_kernel_map_iso_comp /- _inst_5: category_theory.is_iso ↝ category_theory.epi
 -/

-- algebra\invertible.lean
#print nonzero_of_invertible /- _inst_1: group_with_zero ↝ monoid_with_zero nontrivial
 -/

-- algebra\iterate_hom.lean
#print ring_hom.iterate_map_sub /- _inst_1: ring ↝ add_group semiring
 -/
#print ring_hom.iterate_map_neg /- _inst_1: ring ↝ add_group semiring
 -/
#print ring_hom.iterate_map_gsmul /- _inst_1: ring ↝ add_group semiring
 -/

-- algebra\lie\basic.lean
#print ring_commutator.has_bracket /- _inst_1: ring ↝ has_sub has_mul
 -/
#print ring_commutator.commutator /- _inst_1: ring ↝ has_sub has_bracket has_mul
 -/
#print lie_ring.of_associative_ring_bracket /- _inst_1: ring ↝ has_sub has_bracket has_mul
 -/
#print lie_module.to_endo_morphism /- _inst_5: module ↝ algebra
 -/
#print lie_algebra.ad /- _inst_3: lie_algebra ↝ algebra
 -/
#print lie_algebra.ad_apply /- _inst_3: lie_algebra ↝ algebra
 -/
#print lie_submodule_lie_module /- _inst_5: module ↝ lie_ring_module
 -/
#print lie_submodule.quotient.lie_submodule_invariant /- _inst_5: module ↝ algebra
 -/
#print lie_submodule.quotient.action_as_endo_map /- _inst_5: module ↝
 -/
#print lie_submodule.quotient.action_as_endo_map_bracket /- _inst_5: module ↝
 -/
#print lie_submodule.quotient.lie_quotient_lie_ring_module /- _inst_5: module ↝
 -/
#print lie_submodule.quotient.lie_quotient_lie_module /- _inst_5: module ↝ lie_ring_module
 -/
#print linear_equiv.lie_conj /- _inst_3: module ↝ algebra
_inst_5: module ↝ algebra
 -/
#print linear_equiv.lie_conj_apply /- _inst_3: module ↝ algebra
_inst_5: module ↝ algebra
 -/
#print linear_equiv.lie_conj_symm /- _inst_3: module ↝ algebra
_inst_5: module ↝ algebra
 -/
#print lie_equiv_matrix' /- _inst_2: decidable_eq ↝
 -/
#print lie_equiv_matrix'_apply /- _inst_2: decidable_eq ↝
 -/
#print lie_equiv_matrix'_symm_apply /- _inst_2: decidable_eq ↝
 -/
#print matrix.lie_conj /- _inst_2: decidable_eq ↝
 -/
#print matrix.lie_conj_apply /- _inst_2: decidable_eq ↝
 -/
#print matrix.lie_conj_symm_apply /- _inst_2: decidable_eq ↝
 -/
#print matrix.reindex_lie_equiv /- _inst_2: decidable_eq ↝
_inst_4: decidable_eq ↝
 -/
#print matrix.reindex_lie_equiv_apply /- _inst_2: decidable_eq ↝
_inst_4: decidable_eq ↝
 -/
#print matrix.reindex_lie_equiv_symm_apply /- _inst_2: decidable_eq ↝
_inst_4: decidable_eq ↝
 -/
#print bilin_form.is_skew_adjoint_bracket /- _inst_3: module ↝
 -/
#print skew_adjoint_lie_subalgebra /- _inst_3: module ↝ algebra
 -/
#print skew_adjoint_lie_subalgebra_equiv /- _inst_3: module ↝ algebra
_inst_5: module ↝ algebra
 -/
#print skew_adjoint_lie_subalgebra_equiv_apply /- _inst_3: module ↝ algebra
_inst_5: module ↝ algebra
 -/
#print skew_adjoint_lie_subalgebra_equiv_symm_apply /- _inst_3: module ↝ algebra
_inst_5: module ↝ algebra
 -/
#print matrix.lie_transpose /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_2: decidable_eq ↝
 -/
#print matrix.is_skew_adjoint_bracket /- _inst_2: decidable_eq ↝
 -/
#print skew_adjoint_matrices_lie_subalgebra /- _inst_2: decidable_eq ↝
 -/
#print mem_skew_adjoint_matrices_lie_subalgebra /- _inst_2: decidable_eq ↝
 -/
#print skew_adjoint_matrices_lie_subalgebra_equiv /- _inst_2: decidable_eq ↝
 -/
#print skew_adjoint_matrices_lie_subalgebra_equiv_apply /- _inst_2: decidable_eq ↝
 -/
#print skew_adjoint_matrices_lie_subalgebra_equiv_transpose /- _inst_2: decidable_eq ↝
_inst_4: decidable_eq ↝
 -/
#print skew_adjoint_matrices_lie_subalgebra_equiv_transpose_apply /- _inst_2: decidable_eq ↝
_inst_4: decidable_eq ↝
 -/
#print mem_skew_adjoint_matrices_lie_subalgebra_unit_smul /- _inst_2: decidable_eq ↝
 -/

-- algebra\lie\classical.lean
#print lie_algebra.matrix_trace_commutator_zero /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.special_linear.sl /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.special_linear.sl_bracket /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.special_linear.E /- _inst_5: decidable_eq ↝
_inst_9: comm_ring ↝ has_one has_zero
 -/
#print lie_algebra.special_linear.E_apply_one /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.special_linear.E_apply_zero /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.special_linear.E_diag_zero /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.special_linear.E_trace_zero /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.special_linear.Eb /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.special_linear.Eb_val /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.special_linear.sl_non_abelian /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.symplectic.J /- _inst_8: decidable_eq ↝
_inst_9: comm_ring ↝ has_one has_zero has_neg
 -/
#print lie_algebra.symplectic.sp /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.so /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.mem_so /- _inst_5: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.indefinite_diagonal /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
_inst_9: comm_ring ↝ has_one has_zero has_neg
 -/
#print lie_algebra.orthogonal.so' /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.Pso /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
_inst_9: comm_ring ↝ has_one has_zero
 -/
#print lie_algebra.orthogonal.Pso_inv /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.is_unit_Pso /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.indefinite_diagonal_transform /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.so_indefinite_equiv /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.so_indefinite_equiv_apply /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.JD /- _inst_8: decidable_eq ↝
_inst_9: comm_ring ↝ has_one has_zero
 -/
#print lie_algebra.orthogonal.type_D /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.PD /- _inst_8: decidable_eq ↝
_inst_9: comm_ring ↝ has_one has_zero has_neg
 -/
#print lie_algebra.orthogonal.S /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.S_as_blocks /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.JD_transform /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.PD_inv /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.is_unit_PD /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.type_D_equiv_so' /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.JB /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.type_B /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.PB /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.PB_inv /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.is_unit_PB /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.JB_transform /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.indefinite_diagonal_assoc /- _inst_8: decidable_eq ↝
 -/
#print lie_algebra.orthogonal.type_B_equiv_so' /- _inst_8: decidable_eq ↝
 -/

-- algebra\lie\universal_enveloping.lean
#print universal_enveloping_algebra.mk_alg_hom /- _inst_3: lie_algebra ↝ algebra
 -/
#print universal_enveloping_algebra.ι /- _inst_3: lie_algebra ↝ algebra
 -/
#print universal_enveloping_algebra.lift /- _inst_3: lie_algebra ↝ algebra
 -/
#print universal_enveloping_algebra.lift_symm_apply /- _inst_3: lie_algebra ↝ algebra
 -/
#print universal_enveloping_algebra.ι_comp_lift /- _inst_3: lie_algebra ↝ algebra
 -/
#print universal_enveloping_algebra.lift_ι_apply /- _inst_3: lie_algebra ↝ algebra
 -/
#print universal_enveloping_algebra.lift_unique /- _inst_3: lie_algebra ↝ algebra
 -/
#print universal_enveloping_algebra.hom_ext /- _inst_3: lie_algebra ↝ algebra
 -/

-- algebra\linear_ordered_comm_group_with_zero.lean
#print one_le_pow_of_one_le' /- _inst_1: linear_ordered_comm_group_with_zero ↝ ordered_comm_monoid
 -/
#print pow_le_one_of_le_one /- _inst_1: linear_ordered_comm_group_with_zero ↝ ordered_comm_monoid
 -/
#print le_of_le_mul_right /- _inst_1: linear_ordered_comm_group_with_zero ↝ ordered_comm_monoid group_with_zero
 -/
#print inv_lt_inv'' /- _inst_1: linear_ordered_comm_group_with_zero ↝ ordered_comm_monoid group_with_zero
 -/
#print inv_le_inv'' /- _inst_1: linear_ordered_comm_group_with_zero ↝ ordered_comm_monoid group_with_zero
 -/

-- algebra\linear_recurrence.lean
#print linear_recurrence.char_poly /- _inst_1: comm_ring ↝ ring comm_semiring
 -/

-- algebra\module\basic.lean
#print add_smul /- _inst_3: semimodule ↝
 -/
#print zero_smul /- _inst_3: semimodule ↝
 -/
#print two_smul /- _inst_3: semimodule ↝
 -/
#print two_smul' /- _inst_3: semimodule ↝
 -/
#print function.injective.semimodule /- _inst_3: semimodule ↝
 -/
#print function.surjective.semimodule /- _inst_3: semimodule ↝
 -/
#print smul_add_hom /- _inst_3: semimodule ↝
 -/
#print smul_add_hom_apply /- _inst_3: semimodule ↝
 -/
#print semimodule.eq_zero_of_zero_eq_one /- _inst_3: semimodule ↝
 -/
#print list.sum_smul /- _inst_3: semimodule ↝
 -/
#print multiset.sum_smul /- _inst_3: semimodule ↝
 -/
#print finset.sum_smul /- _inst_3: semimodule ↝
 -/
#print semimodule.add_comm_monoid_to_add_comm_group /- _inst_3: semimodule ↝
 -/
#print module /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#print neg_one_smul /- _inst_3: module ↝
 -/
#print smul_eq_zero /- _inst_4: division_ring ↝ group_with_zero ring
_inst_6: module ↝
 -/
#print semimodule.subsingleton /- _inst_4: semimodule ↝
 -/
#print smul_eq_mul /- _inst_1: semiring ↝ has_mul
 -/
#print vector_space /- _inst_1: field ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#print semimodule.smul_eq_smul /- _inst_3: semimodule ↝
 -/
#print semimodule.nsmul_eq_smul /- _inst_3: semimodule ↝
 -/
#print add_monoid_hom.map_nat_cast_smul /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print add_monoid_hom.map_rat_cast_smul /- _inst_4: module ↝
_inst_6: module ↝
 -/

-- algebra\module\linear_map.lean
#print linear_map.to_mul_action_hom /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print linear_map.to_add_hom /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print linear_map.has_coe_to_fun /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.coe_mk /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.id /- _inst_5: semimodule ↝
 -/
#print linear_map.id_apply /- _inst_5: semimodule ↝
 -/
#print linear_map.id_coe /- _inst_5: semimodule ↝
 -/
#print linear_map.to_fun_eq_coe /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.is_linear /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.coe_injective /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ext /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.congr_arg /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.congr_fun /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ext_iff /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_add /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_smul /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_smul_of_tower /- _inst_10: semimodule ↝
_inst_11: is_scalar_tower ↝
_inst_13: semimodule ↝
_inst_14: is_scalar_tower ↝
 -/
#print linear_map.map_zero /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.is_add_monoid_hom /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.to_add_monoid_hom /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.to_add_monoid_hom_coe /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.restrict_scalars /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: is_scalar_tower ↝
_inst_12: is_scalar_tower ↝
 -/
#print linear_map.map_sum /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.to_add_monoid_hom_injective /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ext_ring /- _inst_5: semimodule ↝
 -/
#print linear_map.inverse /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_neg /- _inst_2: add_comm_group ↝ add_comm_monoid add_group
_inst_3: add_comm_group ↝ add_comm_monoid add_group
 -/
#print linear_map.map_sub /- _inst_2: add_comm_group ↝ add_comm_monoid add_group
_inst_3: add_comm_group ↝ add_comm_monoid add_group
 -/
#print linear_map.is_add_group_hom /- _inst_2: add_comm_group ↝ add_comm_monoid add_group
_inst_3: add_comm_group ↝ add_comm_monoid add_group
 -/
#print is_linear_map.mk' /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print is_linear_map.mk'_apply /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print is_linear_map.is_linear_map_smul /- _inst_6: comm_semiring ↝ comm_semigroup semiring
_inst_8: semimodule ↝
 -/
#print is_linear_map.is_linear_map_smul' /- _inst_8: semimodule ↝
 -/
#print is_linear_map.map_zero /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print is_linear_map.is_linear_map_neg /- _inst_4: semimodule ↝
 -/
#print is_linear_map.map_neg /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print is_linear_map.map_sub /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print module.End /- _inst_3: semimodule ↝
 -/
#print linear_equiv.to_linear_map /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print linear_equiv.to_add_equiv /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print linear_equiv.linear_map.has_coe /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.has_coe_to_fun /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.mk_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.to_equiv /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.injective_to_equiv /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.to_equiv_inj /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.injective_to_linear_map /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.to_linear_map_inj /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.refl /- _inst_6: semimodule ↝
 -/
#print linear_equiv.refl_apply /- _inst_6: semimodule ↝
 -/
#print linear_equiv.simps.inv_fun /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.trans_symm /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.symm_trans /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.refl_to_linear_map /- _inst_6: semimodule ↝
 -/
#print linear_equiv.comp_coe /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_equiv.of_involutive /- _inst_6: semimodule ↝
 -/
#print linear_equiv.coe_of_involutive /- _inst_6: semimodule ↝
 -/

-- algebra\module\opposites.lean
#print opposite.semimodule /- _inst_3: semimodule ↝
 -/
#print opposite.op_linear_equiv /- _inst_3: semimodule ↝
 -/
#print opposite.coe_op_linear_equiv /- _inst_3: semimodule ↝
 -/
#print opposite.coe_op_linear_equiv_symm /- _inst_3: semimodule ↝
 -/
#print opposite.coe_op_linear_equiv_to_linear_map /- _inst_3: semimodule ↝
 -/
#print opposite.coe_op_linear_equiv_symm_to_linear_map /- _inst_3: semimodule ↝
 -/
#print opposite.op_linear_equiv_to_add_equiv /- _inst_3: semimodule ↝
 -/
#print opposite.op_linear_equiv_symm_to_add_equiv /- _inst_3: semimodule ↝
 -/

-- algebra\module\ordered.lean
#print smul_lt_smul_of_pos /- _inst_3: semimodule ↝
 -/
#print smul_le_smul_of_nonneg /- _inst_3: semimodule ↝
 -/
#print eq_of_smul_eq_smul_of_pos_of_le /- _inst_3: semimodule ↝
 -/
#print lt_of_smul_lt_smul_of_nonneg /- _inst_3: semimodule ↝
 -/
#print smul_lt_smul_iff_of_pos /- _inst_3: semimodule ↝
 -/
#print smul_pos_iff_of_pos /- _inst_3: semimodule ↝
 -/
#print ordered_semimodule.mk'' /- _inst_3: semimodule ↝
 -/
#print ordered_semimodule.mk' /- _inst_1: linear_ordered_field ↝ group_with_zero linear_ordered_semiring
_inst_3: semimodule ↝
 -/
#print smul_le_smul_iff_of_pos /- _inst_2: ordered_add_comm_group ↝ ordered_add_comm_monoid
_inst_3: semimodule ↝
 -/
#print smul_le_smul_iff_of_neg /- _inst_3: semimodule ↝
 -/
#print smul_lt_iff_of_pos /- _inst_1: linear_ordered_field ↝ group_with_zero ordered_semiring
_inst_2: ordered_add_comm_group ↝ ordered_add_comm_monoid
_inst_3: semimodule ↝
 -/
#print smul_le_iff_of_pos /- _inst_3: semimodule ↝
 -/
#print le_smul_iff_of_pos /- _inst_3: semimodule ↝
 -/
#print prod.ordered_semimodule /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print pi.ordered_semimodule' /- _inst_1: linear_ordered_field ↝ ordered_semimodule ordered_semiring
_inst_9: semimodule ↝
 -/
#print order_dual.has_scalar /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid
_inst_3: semimodule ↝ has_scalar
 -/
#print order_dual.mul_action /- _inst_3: semimodule ↝
 -/
#print order_dual.distrib_mul_action /- _inst_3: semimodule ↝
 -/
#print order_dual.semimodule /- _inst_3: semimodule ↝
 -/
#print order_dual.ordered_semimodule /- _inst_3: semimodule ↝
 -/

-- algebra\module\prod.lean
#print prod.semimodule /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/

-- algebra\module\submodule.lean
#print submodule.to_add_submonoid /- _inst_3: semimodule ↝
 -/
#print submodule.set.has_coe_t /- _inst_3: semimodule ↝
 -/
#print submodule.has_mem /- _inst_3: semimodule ↝
 -/
#print submodule.has_coe_to_sort /- _inst_3: semimodule ↝
 -/
#print submodule.coe_sort_coe /- _inst_3: semimodule ↝
 -/
#print submodule.exists /- _inst_3: semimodule ↝
 -/
#print submodule.forall /- _inst_3: semimodule ↝
 -/
#print submodule.coe_injective /- _inst_3: semimodule ↝
 -/
#print submodule.coe_set_eq /- _inst_3: semimodule ↝
 -/
#print submodule.ext'_iff /- _inst_3: semimodule ↝
 -/
#print submodule.ext /- _inst_3: semimodule ↝
 -/
#print submodule.to_add_submonoid_injective /- _inst_3: semimodule ↝
 -/
#print submodule.to_add_submonoid_eq /- _inst_3: semimodule ↝
 -/
#print submodule.smul_mem_iff /- _inst_1: division_ring ↝ group_with_zero ring
 -/

-- algebra\module\ulift.lean
#print ulift.is_scalar_tower /- _inst_4: is_scalar_tower ↝
 -/
#print ulift.is_scalar_tower' /- _inst_4: is_scalar_tower ↝
 -/
#print ulift.is_scalar_tower'' /- _inst_4: is_scalar_tower ↝
 -/
#print ulift.mul_action /- _inst_2: mul_action ↝
 -/
#print ulift.mul_action' /- _inst_2: mul_action ↝
 -/
#print ulift.distrib_mul_action /- _inst_3: distrib_mul_action ↝
 -/
#print ulift.distrib_mul_action' /- _inst_3: distrib_mul_action ↝
 -/
#print ulift.semimodule /- _inst_3: semimodule ↝
 -/
#print ulift.semimodule' /- _inst_3: semimodule ↝
 -/
#print ulift.semimodule_equiv /- _inst_3: semimodule ↝
 -/

-- algebra\monoid_algebra.lean
#print monoid_algebra /- _inst_1: semiring ↝ has_zero
 -/
#print monoid_algebra.has_mul /- _inst_2: monoid ↝ has_mul
 -/
#print monoid_algebra.has_one /- _inst_2: monoid ↝ has_one
 -/
#print monoid_algebra.nontrivial /- _inst_3: monoid ↝ nonempty
 -/
#print monoid_algebra.add_group /- _inst_1: ring ↝ add_group semiring
 -/
#print monoid_algebra.has_scalar /- _inst_3: semimodule ↝ has_scalar
 -/
#print monoid_algebra.semimodule /- _inst_3: semimodule ↝
 -/
#print monoid_algebra.single_one_comm /- _inst_1: comm_semiring ↝ comm_semigroup semiring
 -/
#print monoid_algebra.group_smul.linear_map /- _inst_6: is_scalar_tower ↝
 -/
#print monoid_algebra.group_smul.linear_map_apply /- _inst_6: is_scalar_tower ↝
 -/
#print monoid_algebra.equivariant_of_linear_of_comm /- _inst_6: is_scalar_tower ↝
_inst_10: is_scalar_tower ↝
 -/
#print monoid_algebra.equivariant_of_linear_of_comm_apply /- _inst_6: is_scalar_tower ↝
_inst_10: is_scalar_tower ↝
 -/
#print add_monoid_algebra /- _inst_1: semiring ↝ has_zero
 -/
#print add_monoid_algebra.has_mul /- _inst_2: add_monoid ↝ has_add
 -/
#print add_monoid_algebra.has_one /- _inst_2: add_monoid ↝ has_zero
 -/
#print add_monoid_algebra.nontrivial /- _inst_3: add_monoid ↝ nonempty
 -/
#print add_monoid_algebra.add_group /- _inst_1: ring ↝ add_group semiring
 -/
#print add_monoid_algebra.has_scalar /- _inst_3: semimodule ↝ has_scalar
 -/
#print add_monoid_algebra.semimodule /- _inst_3: semimodule ↝
 -/

-- algebra\opposites.lean
#print opposite.mul_action /- _inst_2: mul_action ↝
 -/
#print opposite.distrib_mul_action /- _inst_3: distrib_mul_action ↝
 -/

-- algebra\order.lean
#print ge_iff_le /- _inst_1: preorder ↝ has_le
 -/
#print gt_iff_lt /- _inst_1: preorder ↝ has_lt
 -/
#print cmp_swap /- _inst_2: decidable_rel ↝
 -/

-- algebra\ordered_field.lean
#print inv_pos /- _inst_1: linear_ordered_field ↝ group_with_zero linear_ordered_semiring
 -/
#print add_halves /- _inst_1: linear_ordered_field ↝ ordered_semiring division_ring comm_group_with_zero
 -/
#print add_self_div_two /- _inst_1: linear_ordered_field ↝ group_with_zero ordered_semiring
 -/
#print mul_sub_mul_div_mul_neg_iff /- _inst_1: linear_ordered_field ↝ field ordered_add_comm_group
 -/
#print mul_sub_mul_div_mul_nonpos_iff /- _inst_1: linear_ordered_field ↝ field ordered_add_comm_group
 -/
#print mul_self_inj_of_nonneg /- _inst_1: linear_ordered_field ↝ ordered_add_comm_group integral_domain
 -/
#print abs_div /- _inst_1: linear_ordered_field ↝ group_with_zero linear_ordered_ring
 -/
#print abs_inv /- _inst_1: linear_ordered_field ↝ group_with_zero linear_ordered_ring
 -/

-- algebra\ordered_group.lean
#print inv_le_inv' /- _inst_1: ordered_comm_group ↝ ordered_comm_monoid group
 -/
#print neg_le_neg /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print inv_lt_inv' /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print neg_lt_neg /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print mul_le_of_le_inv_mul /- _inst_1: ordered_comm_group ↝ ordered_comm_monoid group
 -/
#print add_le_of_le_neg_add /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print le_neg_add_of_add_le /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print le_inv_mul_of_mul_le /- _inst_1: ordered_comm_group ↝ ordered_comm_monoid group
 -/
#print le_add_of_neg_add_le /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print le_mul_of_inv_mul_le /- _inst_1: ordered_comm_group ↝ ordered_comm_monoid group
 -/
#print inv_mul_le_of_le_mul /- _inst_1: ordered_comm_group ↝ ordered_comm_monoid group
 -/
#print neg_add_le_of_le_add /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print mul_lt_of_lt_inv_mul /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print add_lt_of_lt_neg_add /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print lt_neg_add_of_add_lt /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print lt_inv_mul_of_mul_lt /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print lt_mul_of_inv_mul_lt /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print lt_add_of_neg_add_lt /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print inv_mul_lt_of_lt_mul /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print neg_add_lt_of_lt_add /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print inv_le_inv_iff /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print neg_le_neg_iff /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print neg_le_iff_add_nonneg /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print inv_le_iff_one_le_mul /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print le_inv_iff_mul_le_one /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print le_neg_iff_add_nonpos /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print neg_lt_neg_iff /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print inv_lt_inv_iff /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print le_inv_mul_iff_mul_le /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print le_neg_add_iff_add_le /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print neg_add_le_iff_le_add /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print inv_mul_le_iff_le_mul /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print lt_neg_add_iff_add_lt /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print lt_inv_mul_iff_mul_lt /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print neg_add_lt_iff_lt_add /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print inv_mul_lt_iff_lt_mul /- _inst_1: ordered_comm_group ↝ ordered_cancel_comm_monoid group
 -/
#print add_neg_le_add_neg_iff /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print div_le_div_iff' /- _inst_1: ordered_comm_group ↝ ordered_comm_monoid group
 -/
#print sub_nonneg_of_le /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print le_of_sub_nonneg /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print sub_nonpos_of_le /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print le_of_sub_nonpos /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print sub_pos_of_lt /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print lt_of_sub_pos /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print sub_neg_of_lt /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print lt_of_sub_neg /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print add_le_of_le_sub_left /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print le_sub_left_of_add_le /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print add_le_of_le_sub_right /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print le_sub_right_of_add_le /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print le_add_of_sub_left_le /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print sub_left_le_of_le_add /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print le_add_of_sub_right_le /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print sub_right_le_of_le_add /- _inst_1: ordered_add_comm_group ↝ ordered_add_comm_monoid add_group
 -/
#print sub_le_sub_right /- _inst_1: ordered_add_comm_group ↝ has_sub ordered_add_comm_monoid has_neg
 -/
#print add_lt_of_lt_sub_left /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print lt_sub_left_of_add_lt /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print add_lt_of_lt_sub_right /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print lt_sub_right_of_add_lt /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print lt_add_of_sub_left_lt /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print sub_left_lt_of_lt_add /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print lt_add_of_sub_right_lt /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print sub_right_lt_of_lt_add /- _inst_1: ordered_add_comm_group ↝ add_group ordered_cancel_add_comm_monoid
 -/
#print sub_lt_sub_right /- _inst_1: ordered_add_comm_group ↝ has_sub has_neg ordered_cancel_add_comm_monoid
 -/
#print sub_le_sub_iff_right /- _inst_1: ordered_add_comm_group ↝ has_sub has_neg ordered_cancel_add_comm_monoid
 -/
#print sub_lt_sub_iff_right /- _inst_1: ordered_add_comm_group ↝ has_sub has_neg ordered_cancel_add_comm_monoid
 -/
#print linear_ordered_add_comm_group.add_lt_add_left /- _inst_1: linear_ordered_add_comm_group ↝ ordered_add_comm_group
 -/
#print min_neg_neg /- _inst_1: linear_ordered_add_comm_group ↝ linear_order ordered_add_comm_group
 -/
#print max_neg_neg /- _inst_1: linear_ordered_add_comm_group ↝ linear_order ordered_add_comm_group
 -/
#print min_sub_sub_right /- _inst_1: linear_ordered_add_comm_group ↝ has_sub has_neg linear_ordered_cancel_add_comm_monoid
 -/
#print max_sub_sub_right /- _inst_1: linear_ordered_add_comm_group ↝ has_sub has_neg linear_ordered_cancel_add_comm_monoid
 -/
#print max_zero_sub_eq_self /- _inst_1: linear_ordered_add_comm_group ↝ linear_order ordered_add_comm_group
 -/
#print abs /- _inst_1: linear_ordered_add_comm_group ↝ linear_order has_neg
 -/
#print eq_zero_of_neg_eq /- _inst_1: linear_ordered_add_comm_group ↝ linear_order ordered_add_comm_group
 -/
#print exists_gt_zero /- _inst_1: linear_ordered_add_comm_group ↝ linear_order ordered_add_comm_group
 -/

-- algebra\ordered_monoid.lean
#print with_zero.zero_lt_coe /- _inst_1: partial_order ↝ preorder
 -/
#print with_zero.coe_le_coe /- _inst_1: partial_order ↝ preorder
 -/
#print with_top.zero_lt_top /- _inst_1: ordered_add_comm_monoid ↝ has_zero partial_order
 -/
#print with_top.zero_lt_coe /- _inst_1: ordered_add_comm_monoid ↝ has_zero partial_order
 -/
#print with_bot.coe_eq_zero /- _inst_1: add_monoid ↝ has_zero
 -/
#print with_bot.bot_add /- _inst_1: ordered_add_comm_monoid ↝ add_semigroup
 -/
#print with_bot.add_bot /- _inst_1: ordered_add_comm_monoid ↝ add_semigroup
 -/
#print mul_le_of_le_one_of_le /- _inst_1: ordered_cancel_comm_monoid ↝ ordered_comm_monoid
 -/
#print add_le_of_nonpos_of_le /- _inst_1: ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid
 -/
#print add_le_of_le_of_nonpos /- _inst_1: ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid
 -/
#print mul_le_of_le_of_le_one /- _inst_1: ordered_cancel_comm_monoid ↝ ordered_comm_monoid
 -/
#print min_add_add_left /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid linear_order
 -/
#print min_add_add_right /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid linear_order
 -/
#print max_add_add_left /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid linear_order
 -/
#print max_add_add_right /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid linear_order
 -/
#print min_le_add_of_nonneg_right /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid linear_order
 -/
#print min_le_add_of_nonneg_left /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid linear_order
 -/
#print max_le_add_of_nonneg /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid linear_order
 -/

-- algebra\ordered_ring.lean
#print zero_lt_one' /- _inst_1: linear_ordered_semiring ↝ nontrivial ordered_semiring
 -/
#print lt_of_mul_lt_mul_left /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print lt_of_mul_lt_mul_right /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print le_of_mul_le_mul_left /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print le_of_mul_le_mul_right /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print pos_and_pos_or_neg_and_neg_of_mul_pos /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print nonneg_of_mul_nonneg_left /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print nonneg_of_mul_nonneg_right /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print neg_of_mul_neg_left /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print neg_of_mul_neg_right /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print nonpos_of_mul_nonpos_left /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print nonpos_of_mul_nonpos_right /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print mul_lt_mul_left /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print mul_lt_mul_right /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print nonpos_of_mul_nonneg_left /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print nonpos_of_mul_nonneg_right /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print neg_of_mul_pos_left /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print neg_of_mul_pos_right /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print linear_ordered_semiring.to_no_top_order /- _inst_2: linear_ordered_semiring ↝ nontrivial ordered_semiring
 -/
#print monotone_mul_left_of_nonneg /- _inst_1: linear_ordered_semiring ↝ ordered_semiring
 -/
#print monotone_mul_right_of_nonneg /- _inst_1: linear_ordered_semiring ↝ ordered_semiring
 -/
#print monotone.mul /- _inst_1: linear_ordered_semiring ↝ ordered_semiring
 -/
#print strict_mono.mul_const /- _inst_2: preorder ↝ has_lt
 -/
#print strict_mono.const_mul /- _inst_2: preorder ↝ has_lt
 -/
#print strict_mono.mul_monotone /- _inst_1: linear_ordered_semiring ↝ ordered_semiring
 -/
#print monotone.mul_strict_mono /- _inst_1: linear_ordered_semiring ↝ ordered_semiring
 -/
#print strict_mono.mul /- _inst_1: linear_ordered_semiring ↝ ordered_semiring
_inst_2: preorder ↝ has_lt
 -/
#print mul_le_mul_of_nonpos_left /- _inst_1: ordered_ring ↝ ordered_semiring ring ordered_add_comm_group
 -/
#print mul_le_mul_of_nonpos_right /- _inst_1: ordered_ring ↝ ordered_semiring ring ordered_add_comm_group
 -/
#print mul_lt_mul_of_neg_left /- _inst_1: ordered_ring ↝ ordered_semiring ring ordered_add_comm_group
 -/
#print mul_lt_mul_of_neg_right /- _inst_1: ordered_ring ↝ ordered_semiring ring ordered_add_comm_group
 -/
#print abs_one /- _inst_1: linear_ordered_ring ↝ linear_ordered_add_comm_group nontrivial ordered_semiring
 -/
#print abs_two /- _inst_1: linear_ordered_ring ↝ linear_ordered_add_comm_group nontrivial ordered_semiring
 -/
#print abs_mul /- _inst_1: linear_ordered_ring ↝ linear_ordered_add_comm_group cancel_monoid_with_zero ordered_semiring ring
 -/
#print abs_mul_abs_self /- _inst_1: linear_ordered_ring ↝ linear_ordered_add_comm_group ring
 -/
#print mul_pos_iff /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_ordered_semiring
 -/
#print mul_nonneg_iff /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_ordered_semiring
 -/
#print mul_self_nonneg /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_order
 -/
#print gt_of_mul_lt_mul_neg_left /- _inst_1: linear_ordered_ring ↝ ring ordered_add_comm_group linear_ordered_semiring
 -/
#print neg_one_lt_zero /- _inst_1: linear_ordered_ring ↝ nontrivial ordered_semiring ordered_add_comm_group
 -/
#print le_of_mul_le_of_one_le /- _inst_1: linear_ordered_ring ↝ linear_ordered_semiring
 -/
#print nonneg_le_nonneg_of_squares_le /- _inst_1: linear_ordered_ring ↝ linear_order ordered_semiring
 -/
#print mul_le_mul_left_of_neg /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_order
 -/
#print mul_le_mul_right_of_neg /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_order
 -/
#print sub_one_lt /- _inst_1: linear_ordered_ring ↝ nontrivial ordered_semiring ordered_add_comm_group
 -/
#print mul_self_pos /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_order
 -/
#print mul_self_le_mul_self_of_le_of_neg_le /- _inst_1: linear_ordered_ring ↝ linear_order ordered_semiring ring ordered_add_comm_group
 -/
#print nonneg_of_mul_nonpos_left /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_order
 -/
#print nonneg_of_mul_nonpos_right /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_order
 -/
#print pos_of_mul_neg_left /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_order
 -/
#print pos_of_mul_neg_right /- _inst_1: linear_ordered_ring ↝ ordered_ring linear_order
 -/
#print sub_le_of_abs_sub_le_left /- _inst_1: linear_ordered_ring ↝ linear_ordered_add_comm_group
 -/
#print sub_lt_of_abs_sub_lt_left /- _inst_1: linear_ordered_ring ↝ linear_ordered_add_comm_group
 -/
#print max_mul_mul_le_max_mul_max /- _inst_1: linear_ordered_comm_ring ↝ comm_semigroup linear_order ordered_semiring
 -/
#print abs_sub_square /- _inst_1: linear_ordered_comm_ring ↝ comm_semigroup linear_ordered_ring
 -/
#print canonically_ordered_semiring.mul_le_mul /- _inst_1: canonically_ordered_comm_semiring ↝ canonically_ordered_add_monoid distrib
 -/
#print canonically_ordered_semiring.zero_lt_one /- _inst_1: canonically_ordered_comm_semiring ↝ canonically_ordered_add_monoid monoid_with_zero
 -/
#print canonically_ordered_semiring.mul_pos /- _inst_1: canonically_ordered_comm_semiring ↝ canonically_ordered_add_monoid no_zero_divisors mul_zero_class
 -/
#print with_top.mul_zero_class /- _inst_1: decidable_eq ↝
 -/
#print with_top.mul_def /- _inst_1: decidable_eq ↝
 -/
#print with_top.mul_top /- _inst_1: decidable_eq ↝
 -/
#print with_top.top_mul /- _inst_1: decidable_eq ↝
 -/
#print with_top.top_mul_top /- _inst_1: decidable_eq ↝
 -/
#print with_top.coe_mul /- _inst_1: decidable_eq ↝
 -/
#print with_top.mul_coe /- _inst_1: decidable_eq ↝
 -/
#print with_top.mul_eq_top_iff /- _inst_1: decidable_eq ↝
 -/
#print with_top.no_zero_divisors /- _inst_1: decidable_eq ↝
 -/
#print with_top.canonically_ordered_comm_semiring /- _inst_1: decidable_eq ↝
 -/

-- algebra\pointwise.lean
#print set.fintype_mul /- _inst_2: decidable_eq ↝
 -/
#print set.fintype_add /- _inst_2: decidable_eq ↝
 -/
#print set.univ_inv /- _inst_1: group ↝ has_inv
 -/
#print set.univ_neg /- _inst_1: add_group ↝ has_neg
 -/
#print set.mul_action_set /- _inst_2: mul_action ↝
 -/
#print zero_smul_set /- _inst_3: semimodule ↝
 -/
#print mem_inv_smul_set_iff /- _inst_1: field ↝ group_with_zero
_inst_2: mul_action ↝
 -/
#print mem_smul_set_iff_inv_smul_mem /- _inst_2: mul_action ↝
 -/
#print finset.has_mul /- _inst_1: decidable_eq ↝
 -/
#print finset.has_add /- _inst_1: decidable_eq ↝
 -/
#print finset.mul_def /- _inst_1: decidable_eq ↝
 -/
#print finset.add_def /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_add /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_mul /- _inst_1: decidable_eq ↝
 -/
#print finset.coe_mul /- _inst_1: decidable_eq ↝
 -/
#print finset.coe_add /- _inst_1: decidable_eq ↝
 -/
#print finset.add_mem_add /- _inst_1: decidable_eq ↝
 -/
#print finset.mul_mem_mul /- _inst_1: decidable_eq ↝
 -/
#print finset.add_card_le /- _inst_1: decidable_eq ↝
 -/
#print finset.mul_card_le /- _inst_1: decidable_eq ↝
 -/

-- algebra\polynomial\big_operators.lean
#print polynomial.nat_degree_prod /- _inst_1: integral_domain ↝ nontrivial no_zero_divisors comm_semiring
 -/

-- algebra\polynomial\group_ring_action.lean
#print prod_X_sub_smul /- _inst_4: comm_ring ↝ ring comm_semiring
_inst_5: mul_semiring_action ↝
 -/

-- algebra\quadratic_discriminant.lean
#print discrim /- _inst_1: ring ↝ has_sub has_one has_add has_mul has_pow
 -/
#print quadratic_eq_zero_iff_discrim_eq_square /- _inst_1: integral_domain ↝ cancel_monoid_with_zero comm_ring
 -/
#print quadratic_eq_zero_iff /- _inst_1: field ↝ comm_group_with_zero integral_domain
 -/
#print discrim_le_zero /- _inst_1: linear_ordered_field ↝ field linear_ordered_ring
 -/

-- algebra\quandle.lean
#print rack.self_distrib /- _inst_1: rack ↝ shelf
 -/
#print rack.is_involutory /- _inst_2: rack ↝ shelf
 -/
#print rack.is_abelian /- _inst_2: rack ↝ shelf
 -/

-- algebra\ring\basic.lean
#print one_add_one_eq_two /- _inst_1: semiring ↝ has_one has_add
 -/
#print two_mul /- _inst_1: semiring ↝ monoid distrib
 -/
#print distrib_three_right /- _inst_1: semiring ↝ distrib
 -/
#print mul_two /- _inst_1: semiring ↝ monoid distrib
 -/
#print mul_boole /- _inst_2: semiring ↝ monoid mul_zero_class
 -/
#print boole_mul /- _inst_2: semiring ↝ monoid mul_zero_class
 -/
#print even /- _inst_1: semiring ↝ has_one has_add has_mul
 -/
#print odd /- _inst_1: semiring ↝ has_one has_add has_mul
 -/
#print add_mul_self_eq /- _inst_1: comm_semiring ↝ comm_semigroup semiring
 -/
#print dvd_add /- _inst_1: comm_semiring ↝ monoid distrib
 -/
#print two_dvd_bit0 /- _inst_1: comm_semiring ↝ semiring
 -/
#print ring_hom.map_dvd /- _inst_1: comm_semiring ↝ semiring
_inst_2: comm_semiring ↝ semiring
 -/
#print neg_mul_eq_neg_mul /- _inst_1: ring ↝ distrib add_group mul_zero_class
 -/
#print neg_mul_eq_mul_neg /- _inst_1: ring ↝ distrib add_group mul_zero_class
 -/
#print ring_hom.map_neg /- _inst_1: ring ↝ add_group semiring
_inst_2: ring ↝ add_group semiring
 -/
#print ring_hom.map_sub /- _inst_1: ring ↝ add_group semiring
_inst_2: ring ↝ add_group semiring
 -/
#print ring_hom.injective_iff /- _inst_1: ring ↝ add_group semiring
 -/
#print dvd_neg_of_dvd /- _inst_1: comm_ring ↝ ring
 -/
#print neg_dvd_of_dvd /- _inst_1: comm_ring ↝ comm_semigroup ring
 -/
#print mul_self_sub_mul_self /- _inst_1: comm_ring ↝ comm_semigroup ring
 -/
#print Vieta_formula_quadratic /- _inst_1: comm_ring ↝ comm_semigroup ring
 -/
#print dvd_mul_sub_mul /- _inst_1: comm_ring ↝ ring comm_semiring
 -/
#print succ_ne_self /- _inst_1: ring ↝ add_monoid monoid_with_zero add_left_cancel_semigroup
 -/
#print pred_ne_self /- _inst_1: ring ↝ monoid_with_zero add_group
 -/
#print mul_self_eq_mul_self_iff /- _inst_1: integral_domain ↝ comm_ring no_zero_divisors
 -/
#print ring.inverse /- _inst_1: ring ↝ monoid has_zero
 -/

-- algebra\ring\prod.lean
#print ring_hom.prod_comp_prod_map /- _inst_1: semiring ↝ monoid
_inst_2: semiring ↝ monoid
_inst_3: semiring ↝ monoid
_inst_4: semiring ↝ monoid
_inst_5: semiring ↝ monoid
 -/

-- algebra\squarefree.lean
#print squarefree_of_dvd_of_squarefree /- _inst_1: comm_monoid ↝ monoid
 -/
#print multiplicity.squarefree_iff_multiplicity_le_one /- _inst_2: decidable_rel ↝
 -/
#print unique_factorization_monoid.squarefree_iff_nodup_factors /- _inst_5: decidable_eq ↝
 -/

-- algebra\star\basic.lean
#print star_neg /- _inst_1: ring ↝ add_group semiring has_star
 -/
#print star_sub /- _inst_1: ring ↝ add_group semiring has_star
 -/
#print star_bit0 /- _inst_1: ring ↝ add_right_cancel_semigroup semiring has_star
 -/

-- analysis\ODE\gronwall.lean
#print norm_le_gronwall_bound_of_norm_deriv_right_le /- _inst_2: normed_space ↝
 -/
#print dist_le_of_approx_trajectories_ODE_of_mem_set /- _inst_2: normed_space ↝
 -/
#print dist_le_of_approx_trajectories_ODE /- _inst_2: normed_space ↝
 -/
#print dist_le_of_trajectories_ODE_of_mem_set /- _inst_2: normed_space ↝
 -/
#print dist_le_of_trajectories_ODE /- _inst_2: normed_space ↝
 -/
#print ODE_solution_unique_of_mem_set /- _inst_2: normed_space ↝
 -/
#print ODE_solution_unique /- _inst_2: normed_space ↝
 -/

-- analysis\analytic\basic.lean
#print formal_multilinear_series.radius /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.le_radius_of_bound /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.bound_of_lt_radius /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.geometric_bound_of_lt_radius /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.min_radius_le_radius_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.radius_neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.partial_sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.partial_sum_continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print analytic_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.has_fpower_series_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_at.analytic_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.analytic_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.radius_pos /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_at.radius_pos /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_at.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print analytic_at.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_at.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print analytic_at.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_at.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print analytic_at.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.coeff_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_at.coeff_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.uniform_geometric_approx /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.tendsto_uniformly_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.tendsto_locally_uniformly_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.tendsto_uniformly_on' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.tendsto_locally_uniformly_on' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.continuous_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_at.continuous_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print analytic_at.continuous_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.has_fpower_series_on_ball /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.continuous_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.change_origin /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.change_origin_summable_aux1 /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.change_origin_summable_aux2 /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.change_origin_summable_aux3 /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.change_origin_radius /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.change_origin_has_sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.change_origin_eval /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.change_origin /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fpower_series_on_ball.analytic_at_of_mem /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_open_analytic_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/

-- analysis\analytic\composition.lean
#print formal_multilinear_series.apply_composition /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.apply_composition_ones /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.apply_composition_update /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.comp_along_composition_multilinear /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_along_composition_multilinear_bound /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_along_composition /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_along_composition_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_along_composition_norm /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_along_composition_nnnorm /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_coeff_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_coeff_zero' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_coeff_zero'' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.id /- _inst_3: normed_space ↝
 -/
#print formal_multilinear_series.id_apply_one /- _inst_3: normed_space ↝
 -/
#print formal_multilinear_series.id_apply_one' /- _inst_3: normed_space ↝
 -/
#print formal_multilinear_series.id_apply_ne_one /- _inst_3: normed_space ↝
 -/
#print formal_multilinear_series.comp_id /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.id_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.comp_summable_nnreal /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.le_comp_radius_of_summable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_partial_sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fpower_series_at.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print analytic_at.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print formal_multilinear_series.comp_assoc /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_9: normed_space ↝
 -/

-- analysis\asymptotics.lean
#print asymptotics.is_O_with.prod_left_same /- _inst_6: normed_group ↝ has_norm
 -/
#print asymptotics.is_O_with.prod_left_fst /- _inst_6: normed_group ↝ has_norm
 -/
#print asymptotics.is_O_with.prod_left_snd /- _inst_6: normed_group ↝ has_norm
 -/
#print asymptotics.is_O.prod_left_fst /- _inst_6: normed_group ↝ has_norm
 -/
#print asymptotics.is_O.prod_left_snd /- _inst_6: normed_group ↝ has_norm
 -/
#print asymptotics.is_o.prod_left_fst /- _inst_6: normed_group ↝ has_norm
 -/
#print asymptotics.is_o.prod_left_snd /- _inst_6: normed_group ↝ has_norm
 -/
#print asymptotics.is_O_refl_left /- _inst_5: normed_group ↝ has_norm
 -/
#print asymptotics.is_O_with_const_one /- _inst_9: normed_field ↝ monoid_with_zero norm_one_class normed_group nontrivial
 -/
#print asymptotics.is_o_one_iff /- _inst_9: normed_field ↝ monoid_with_zero normed_group nontrivial
 -/
#print asymptotics.is_O_one_of_tendsto /- _inst_9: normed_field ↝ monoid_with_zero normed_group nontrivial
 -/
#print asymptotics.is_O_self_const_mul /- _inst_9: normed_field ↝ group_with_zero normed_ring
 -/
#print asymptotics.is_O_const_mul_left_iff /- _inst_9: normed_field ↝ group_with_zero normed_ring
 -/
#print asymptotics.is_o_const_mul_left_iff /- _inst_9: normed_field ↝ group_with_zero normed_ring
 -/
#print asymptotics.is_O.const_mul_right /- _inst_9: normed_field ↝ group_with_zero normed_ring
 -/
#print asymptotics.is_O_const_mul_right_iff /- _inst_9: normed_field ↝ group_with_zero normed_ring
 -/
#print asymptotics.is_o.const_mul_right /- _inst_9: normed_field ↝ group_with_zero normed_ring
 -/
#print asymptotics.is_o_const_mul_right_iff /- _inst_9: normed_field ↝ group_with_zero normed_ring
 -/
#print asymptotics.is_O_with.const_smul_left /- _inst_11: normed_space ↝
 -/
#print asymptotics.is_O_const_smul_left_iff /- _inst_11: normed_space ↝
 -/
#print asymptotics.is_o_const_smul_left /- _inst_11: normed_space ↝
 -/
#print asymptotics.is_o_const_smul_left_iff /- _inst_11: normed_space ↝
 -/
#print asymptotics.is_O_const_smul_right /- _inst_11: normed_space ↝
 -/
#print asymptotics.is_o_const_smul_right /- _inst_11: normed_space ↝
 -/
#print asymptotics.is_O_with.smul /- _inst_11: normed_space ↝
_inst_12: normed_space ↝
 -/
#print asymptotics.is_O.smul /- _inst_11: normed_space ↝
_inst_12: normed_space ↝
 -/
#print asymptotics.is_O.smul_is_o /- _inst_11: normed_space ↝
_inst_12: normed_space ↝
 -/
#print asymptotics.is_o.smul_is_O /- _inst_11: normed_space ↝
_inst_12: normed_space ↝
 -/
#print asymptotics.is_o.smul /- _inst_11: normed_space ↝
_inst_12: normed_space ↝
 -/
#print asymptotics.is_O_with.eventually_mul_div_cancel /- _inst_9: normed_field ↝ group_with_zero normed_group
 -/

-- analysis\calculus\deriv.lean
#print has_deriv_at_filter /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_at /- _inst_3: normed_space ↝
 -/
#print has_strict_deriv_at /- _inst_3: normed_space ↝
 -/
#print deriv_within /- _inst_3: normed_space ↝
 -/
#print deriv /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at_filter_iff_has_deriv_at_filter /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at_filter.has_deriv_at_filter /- _inst_3: normed_space ↝
 -/
#print has_fderiv_within_at_iff_has_deriv_within_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at_iff_has_fderiv_within_at /- _inst_3: normed_space ↝
 -/
#print has_fderiv_within_at.has_deriv_within_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.has_fderiv_within_at /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at_iff_has_deriv_at /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at.has_deriv_at /- _inst_3: normed_space ↝
 -/
#print has_strict_fderiv_at_iff_has_strict_deriv_at /- _inst_3: normed_space ↝
 -/
#print has_strict_fderiv_at.has_strict_deriv_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_iff_has_fderiv_at /- _inst_3: normed_space ↝
 -/
#print deriv_within_zero_of_not_differentiable_within_at /- _inst_3: normed_space ↝
 -/
#print deriv_zero_of_not_differentiable_at /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at.eq_deriv /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter_iff_tendsto /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at_iff_tendsto /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_iff_tendsto /- _inst_3: normed_space ↝
 -/
#print has_strict_deriv_at.has_deriv_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter_iff_tendsto_slope /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at_iff_tendsto_slope /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at_iff_tendsto_slope' /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_iff_tendsto_slope /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_iff_is_o_nhds_zero /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.mono /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.mono /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.has_deriv_at_filter /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.has_deriv_within_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.differentiable_within_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.differentiable_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at_univ /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_unique /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at_inter' /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at_inter /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.union /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.nhds_within /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.has_deriv_at /- _inst_3: normed_space ↝
 -/
#print differentiable_within_at.has_deriv_within_at /- _inst_3: normed_space ↝
 -/
#print differentiable_at.has_deriv_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.deriv /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.deriv_within /- _inst_3: normed_space ↝
 -/
#print fderiv_within_deriv_within /- _inst_3: normed_space ↝
 -/
#print deriv_within_fderiv_within /- _inst_3: normed_space ↝
 -/
#print fderiv_deriv /- _inst_3: normed_space ↝
 -/
#print deriv_fderiv /- _inst_3: normed_space ↝
 -/
#print differentiable_at.deriv_within /- _inst_3: normed_space ↝
 -/
#print deriv_within_subset /- _inst_3: normed_space ↝
 -/
#print deriv_within_univ /- _inst_3: normed_space ↝
 -/
#print deriv_within_inter /- _inst_3: normed_space ↝
 -/
#print deriv_within_of_open /- _inst_3: normed_space ↝
 -/
#print filter.eventually_eq.has_deriv_at_filter_iff /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.congr_of_eventually_eq /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.congr_mono /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.congr /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
 -/
#print filter.eventually_eq.deriv_within_eq /- _inst_3: normed_space ↝
 -/
#print deriv_within_congr /- _inst_3: normed_space ↝
 -/
#print filter.eventually_eq.deriv_eq /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter_const /- _inst_3: normed_space ↝
 -/
#print has_strict_deriv_at_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_const /- _inst_3: normed_space ↝
 -/
#print deriv_const /- _inst_3: normed_space ↝
 -/
#print deriv_const' /- _inst_3: normed_space ↝
 -/
#print deriv_within_const /- _inst_3: normed_space ↝
 -/
#print continuous_linear_map.has_deriv_at_filter /- _inst_3: normed_space ↝
 -/
#print continuous_linear_map.has_strict_deriv_at /- _inst_3: normed_space ↝
 -/
#print continuous_linear_map.has_deriv_at /- _inst_3: normed_space ↝
 -/
#print continuous_linear_map.has_deriv_within_at /- _inst_3: normed_space ↝
 -/
#print continuous_linear_map.deriv /- _inst_3: normed_space ↝
 -/
#print continuous_linear_map.deriv_within /- _inst_3: normed_space ↝
 -/
#print linear_map.has_deriv_at_filter /- _inst_3: normed_space ↝
 -/
#print linear_map.has_strict_deriv_at /- _inst_3: normed_space ↝
 -/
#print linear_map.has_deriv_at /- _inst_3: normed_space ↝
 -/
#print linear_map.has_deriv_within_at /- _inst_3: normed_space ↝
 -/
#print linear_map.deriv /- _inst_3: normed_space ↝
 -/
#print linear_map.deriv_within /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.add /- _inst_3: normed_space ↝
 -/
#print has_strict_deriv_at.add /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.add /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.add /- _inst_3: normed_space ↝
 -/
#print deriv_within_add /- _inst_3: normed_space ↝
 -/
#print deriv_add /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.add_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.add_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.add_const /- _inst_3: normed_space ↝
 -/
#print deriv_within_add_const /- _inst_3: normed_space ↝
 -/
#print deriv_add_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.const_add /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.const_add /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.const_add /- _inst_3: normed_space ↝
 -/
#print deriv_within_const_add /- _inst_3: normed_space ↝
 -/
#print deriv_const_add /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.sum /- _inst_3: normed_space ↝
 -/
#print has_strict_deriv_at.sum /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.sum /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.sum /- _inst_3: normed_space ↝
 -/
#print deriv_within_sum /- _inst_3: normed_space ↝
 -/
#print deriv_sum /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.smul /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.smul /- _inst_3: normed_space ↝
 -/
#print has_strict_deriv_at.smul /- _inst_3: normed_space ↝
 -/
#print deriv_within_smul /- _inst_3: normed_space ↝
 -/
#print deriv_smul /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.smul_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.smul_const /- _inst_3: normed_space ↝
 -/
#print deriv_within_smul_const /- _inst_3: normed_space ↝
 -/
#print deriv_smul_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.const_smul /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.const_smul /- _inst_3: normed_space ↝
 -/
#print deriv_within_const_smul /- _inst_3: normed_space ↝
 -/
#print deriv_const_smul /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.neg /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.neg /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.neg /- _inst_3: normed_space ↝
 -/
#print has_strict_deriv_at.neg /- _inst_3: normed_space ↝
 -/
#print deriv_within.neg /- _inst_3: normed_space ↝
 -/
#print deriv.neg /- _inst_3: normed_space ↝
 -/
#print deriv.neg' /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.sub /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.sub /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.sub /- _inst_3: normed_space ↝
 -/
#print has_strict_deriv_at.sub /- _inst_3: normed_space ↝
 -/
#print deriv_within_sub /- _inst_3: normed_space ↝
 -/
#print deriv_sub /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.is_O_sub /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.sub_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.sub_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.sub_const /- _inst_3: normed_space ↝
 -/
#print deriv_within_sub_const /- _inst_3: normed_space ↝
 -/
#print deriv_sub_const /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.const_sub /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.const_sub /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.const_sub /- _inst_3: normed_space ↝
 -/
#print deriv_within_const_sub /- _inst_3: normed_space ↝
 -/
#print deriv_const_sub /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.tendsto_nhds /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.continuous_within_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.continuous_at /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.prod /- _inst_3: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_deriv_within_at.prod /- _inst_3: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_deriv_at.prod /- _inst_3: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_deriv_at_filter.scomp /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.scomp /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.scomp /- _inst_3: normed_space ↝
 -/
#print has_strict_deriv_at.scomp /- _inst_3: normed_space ↝
 -/
#print has_deriv_at.scomp_has_deriv_within_at /- _inst_3: normed_space ↝
 -/
#print deriv_within.scomp /- _inst_3: normed_space ↝
 -/
#print deriv.scomp /- _inst_3: normed_space ↝
 -/
#print has_deriv_at_filter.comp_has_fderiv_at_filter /- _inst_5: normed_space ↝
 -/
#print has_deriv_at.comp_has_fderiv_at /- _inst_5: normed_space ↝
 -/
#print has_deriv_at.comp_has_fderiv_within_at /- _inst_5: normed_space ↝
 -/
#print has_deriv_within_at.comp_has_fderiv_within_at /- _inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.comp_has_deriv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.comp_has_deriv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.comp_has_deriv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within.comp_deriv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv.comp_deriv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_deriv_within_at.limsup_norm_slope_le /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.limsup_slope_norm_le /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.liminf_right_norm_slope_le /- _inst_3: normed_space ↝
 -/
#print has_deriv_within_at.liminf_right_slope_norm_le /- _inst_3: normed_space ↝
 -/

-- analysis\calculus\extend_deriv.lean
#print has_fderiv_at_boundary_of_tendsto_fderiv /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print has_deriv_at_interval_left_endpoint_of_tendsto_deriv /- _inst_2: normed_space ↝
 -/
#print has_deriv_at_interval_right_endpoint_of_tendsto_deriv /- _inst_2: normed_space ↝
 -/
#print has_deriv_at_of_has_deriv_at_of_ne /- _inst_2: normed_space ↝
 -/

-- analysis\calculus\fderiv.lean
#print has_fderiv_at_filter /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_zero_of_not_differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_zero_of_not_differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.lim /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.unique_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print unique_diff_within_at.eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print unique_diff_on.eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter_iff_tendsto /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at_iff_tendsto /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_iff_tendsto /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_iff_is_o_nhds_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.le_of_lip /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.has_fderiv_at_filter /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at_univ /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.is_O_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.is_O_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.lim /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_unique /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at_inter' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at_inter /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.union /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.nhds_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_at.le_of_lip /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at_of_not_mem_closure /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at_univ /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at_inter /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at_inter' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on_univ /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on_of_locally_differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_subset /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_univ /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_inter /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_of_open /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_eq_fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_mem_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.tendsto_nhds /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.continuous_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.continuous_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.continuous_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.continuous_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.continuous_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.continuous_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.is_O_sub_rev /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.is_O_sub_rev /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print filter.eventually_eq.has_strict_fderiv_at_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print filter.eventually_eq.has_fderiv_at_filter_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.congr_mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.congr_mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.congr_mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on_congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.fderiv_within_congr_mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print filter.eventually_eq.fderiv_within_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print filter.eventually_eq.fderiv_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at_id /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at_filter_id /- _inst_3: normed_space ↝
 -/
#print has_fderiv_within_at_id /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at_id /- _inst_3: normed_space ↝
 -/
#print differentiable_at_id /- _inst_3: normed_space ↝
 -/
#print differentiable_at_id' /- _inst_3: normed_space ↝
 -/
#print differentiable_within_at_id /- _inst_3: normed_space ↝
 -/
#print differentiable_id /- _inst_3: normed_space ↝
 -/
#print differentiable_id' /- _inst_3: normed_space ↝
 -/
#print differentiable_on_id /- _inst_3: normed_space ↝
 -/
#print fderiv_id /- _inst_3: normed_space ↝
 -/
#print fderiv_id' /- _inst_3: normed_space ↝
 -/
#print fderiv_within_id /- _inst_3: normed_space ↝
 -/
#print fderiv_within_id' /- _inst_3: normed_space ↝
 -/
#print has_strict_fderiv_at_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_const_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_const_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.has_strict_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.has_fderiv_at_filter /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.has_fderiv_at_filter /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_within_at.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_at.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_at.comp_has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_within_at.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_within_at.comp' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_at.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_at.comp_differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print fderiv_within.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print fderiv.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print fderiv.comp_fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_on.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable.comp_differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable.iterate /- _inst_3: normed_space ↝
 -/
#print differentiable_on.iterate /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at_filter.iterate /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at.iterate /- _inst_3: normed_space ↝
 -/
#print has_fderiv_within_at.iterate /- _inst_3: normed_space ↝
 -/
#print has_strict_fderiv_at.iterate /- _inst_3: normed_space ↝
 -/
#print differentiable_at.iterate /- _inst_3: normed_space ↝
 -/
#print differentiable_within_at.iterate /- _inst_3: normed_space ↝
 -/
#print has_strict_fderiv_at.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_at_filter.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_within_at.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_at.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_within_at.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_at.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_on.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_at.fderiv_prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_at.fderiv_within_prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_at_filter_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_at_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_within_at_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_at_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_within_at_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_on_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print fderiv_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print fderiv_within_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_at_filter_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_at_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_fderiv_within_at_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_at_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_within_at_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print differentiable_on_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print fderiv_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print fderiv_within_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.prod_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_9: normed_space ↝
 -/
#print has_fderiv_at.prod_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_9: normed_space ↝
 -/
#print differentiable_at.prod_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_9: normed_space ↝
 -/
#print has_strict_fderiv_at.const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_const_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_add_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_const_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_sub_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter.const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_const_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_bilinear_map.has_strict_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.continuous_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.continuous_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.is_open /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.nhds /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.smul_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.smul_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.smul_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_within_at.smul_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_at.smul_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable_on.smul_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print differentiable.smul_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_within_smul_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_smul_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.mul /- _inst_3: normed_space ↝
 -/
#print has_fderiv_within_at.mul /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at.mul /- _inst_3: normed_space ↝
 -/
#print differentiable_within_at.mul /- _inst_3: normed_space ↝
 -/
#print differentiable_at.mul /- _inst_3: normed_space ↝
 -/
#print differentiable_on.mul /- _inst_3: normed_space ↝
 -/
#print differentiable.mul /- _inst_3: normed_space ↝
 -/
#print fderiv_within_mul /- _inst_3: normed_space ↝
 -/
#print fderiv_mul /- _inst_3: normed_space ↝
 -/
#print has_strict_fderiv_at.mul_const /- _inst_3: normed_space ↝
 -/
#print has_fderiv_within_at.mul_const /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at.mul_const /- _inst_3: normed_space ↝
 -/
#print differentiable_within_at.mul_const /- _inst_3: normed_space ↝
 -/
#print differentiable_at.mul_const /- _inst_3: normed_space ↝
 -/
#print differentiable_on.mul_const /- _inst_3: normed_space ↝
 -/
#print differentiable.mul_const /- _inst_3: normed_space ↝
 -/
#print fderiv_within_mul_const /- _inst_3: normed_space ↝
 -/
#print fderiv_mul_const /- _inst_3: normed_space ↝
 -/
#print has_strict_fderiv_at.const_mul /- _inst_3: normed_space ↝
 -/
#print has_fderiv_within_at.const_mul /- _inst_3: normed_space ↝
 -/
#print has_fderiv_at.const_mul /- _inst_3: normed_space ↝
 -/
#print differentiable_within_at.const_mul /- _inst_3: normed_space ↝
 -/
#print differentiable_at.const_mul /- _inst_3: normed_space ↝
 -/
#print differentiable_on.const_mul /- _inst_3: normed_space ↝
 -/
#print differentiable.const_mul /- _inst_3: normed_space ↝
 -/
#print fderiv_within_const_mul /- _inst_3: normed_space ↝
 -/
#print fderiv_const_mul /- _inst_3: normed_space ↝
 -/
#print continuous_linear_equiv.has_strict_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.comp_differentiable_within_at_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_differentiable_at_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_differentiable_on_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_differentiable_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_has_fderiv_within_at_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_has_strict_fderiv_at_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_has_fderiv_at_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_has_fderiv_within_at_iff' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_has_fderiv_at_iff' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.of_local_left_inverse /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.of_local_left_inverse /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at.of_local_homeomorph /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_at_filter_real_equiv /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print has_fderiv_at.lim_real /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print has_fderiv_within_at.maps_to_tangent_cone /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.unique_diff_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_fderiv_within_at.unique_diff_within_at_of_continuous_linear_equiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.unique_diff_on_preimage_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.restrict_scalars /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: is_scalar_tower ↝
_inst_9: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
 -/
#print has_fderiv_at.restrict_scalars /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: is_scalar_tower ↝
_inst_9: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
 -/
#print has_fderiv_within_at.restrict_scalars /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: is_scalar_tower ↝
_inst_9: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
 -/
#print differentiable_at.restrict_scalars /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: is_scalar_tower ↝
_inst_9: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
 -/
#print differentiable_within_at.restrict_scalars /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: is_scalar_tower ↝
_inst_9: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
 -/
#print differentiable_on.restrict_scalars /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: is_scalar_tower ↝
_inst_9: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
 -/
#print differentiable.restrict_scalars /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: is_scalar_tower ↝
_inst_9: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
 -/
#print has_strict_fderiv_at.smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print has_fderiv_within_at.smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print has_fderiv_at.smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable_within_at.smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable_at.smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable_on.smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable.smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print fderiv_within_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print fderiv_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print has_strict_fderiv_at.smul_algebra_const /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print has_fderiv_within_at.smul_algebra_const /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print has_fderiv_at.smul_algebra_const /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable_within_at.smul_algebra_const /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable_at.smul_algebra_const /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable_on.smul_algebra_const /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable.smul_algebra_const /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print fderiv_within_smul_algebra_const /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print fderiv_smul_algebra_const /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print has_strict_fderiv_at.const_smul_algebra /- _inst_2: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_algebra ↝ has_scalar
_inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝ has_scalar
_inst_9: is_scalar_tower ↝ has_scalar
 -/
#print has_fderiv_at_filter.const_smul_algebra /- _inst_2: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_algebra ↝ has_scalar
_inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝ has_scalar
_inst_9: is_scalar_tower ↝ has_scalar
 -/
#print has_fderiv_within_at.const_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print has_fderiv_at.const_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable_within_at.const_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable_at.const_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable_on.const_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print differentiable.const_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print fderiv_within_const_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/
#print fderiv_const_smul_algebra /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: normed_space ↝
_inst_9: is_scalar_tower ↝
 -/

-- analysis\calculus\fderiv_measurable.lean
#print continuous_linear_map.measurable_space /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.borel_space /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.measurable_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.measurable_apply' /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.measurable_apply₂ /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.measurable_coe /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.A /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.B /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.D /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.is_open_A /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.is_open_B /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.A_mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.le_of_mem_A /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.mem_A_of_differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.norm_sub_le_of_mem_A /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.differentiable_set_subset_D /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.D_subset_differentiable_set /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print fderiv_measurable_aux.differentiable_set_eq_D /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_measurable_set_of_differentiable_at_of_is_complete /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_measurable_set_of_differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print measurable_fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print measurable_fderiv_apply_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print measurable_deriv /- _inst_5: normed_space ↝
 -/

-- analysis\calculus\implicit.lean
#print implicit_function_data.prod_fun /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.prod_fun_apply /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.has_strict_fderiv_at /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.to_local_homeomorph /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.implicit_function /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.to_local_homeomorph_coe /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.to_local_homeomorph_apply /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.pt_mem_to_local_homeomorph_source /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.map_pt_mem_to_local_homeomorph_target /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.prod_map_implicit_function /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.left_map_implicit_function /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.right_map_implicit_function /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.implicit_function_apply_image /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print implicit_function_data.implicit_function_has_strict_fderiv_at /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
_inst_9: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_function_data_of_complemented /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_function_of_complemented /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_fst /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_apply /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_apply_ker /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_self /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.mem_implicit_to_local_homeomorph_of_complemented_source /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.mem_implicit_to_local_homeomorph_of_complemented_target /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.map_implicit_function_of_complemented_eq /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.eq_implicit_function_of_complemented /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.to_implicit_function_of_complemented /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_to_local_homeomorph /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_function /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_to_local_homeomorph_fst /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_to_local_homeomorph_apply_ker /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.implicit_to_local_homeomorph_self /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.mem_implicit_to_local_homeomorph_source /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.mem_implicit_to_local_homeomorph_target /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.map_implicit_function_eq /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.eq_implicit_function /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_strict_fderiv_at.to_implicit_function /- _inst_4: normed_space ↝
_inst_7: normed_space ↝
 -/

-- analysis\calculus\inverse.lean
#print approximates_linear_on /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.mono_num /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.mono_set /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.lipschitz_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.lipschitz /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.continuous_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.antilipschitz /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.injective /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.inj_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.to_local_equiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.inverse_continuous_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.inverse_approx_map /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.inverse_approx_map_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.inverse_approx_map_dist_self /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.inverse_approx_map_dist_self_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.inverse_approx_map_fixed_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.inverse_approx_map_contracts_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.inverse_approx_map_maps_to /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.surj_on_closed_ball /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.to_local_homeomorph /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.to_local_homeomorph_coe /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.to_local_homeomorph_source /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.to_local_homeomorph_target /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print approximates_linear_on.closed_ball_subset_target /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.approximates_deriv_on_nhds /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.approximates_deriv_on_open_nhds /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.to_local_homeomorph /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.to_local_homeomorph_coe /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.mem_to_local_homeomorph_source /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.image_mem_to_local_homeomorph_target /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.local_inverse /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.eventually_left_inverse /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.local_inverse_apply_image /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.eventually_right_inverse /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.local_inverse_continuous_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.local_inverse_tendsto /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.local_inverse_unique /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.to_local_inverse /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_strict_fderiv_at.to_local_left_inverse /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.to_local_homeomorph /- _inst_11: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_diff_at.to_local_homeomorph_coe /- _inst_11: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_diff_at.mem_to_local_homeomorph_source /- _inst_11: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_diff_at.image_mem_to_local_homeomorph_target /- _inst_11: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_diff_at.local_inverse /- _inst_11: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_diff_at.local_inverse_apply_image /- _inst_11: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_diff_at.to_local_inverse /- _inst_11: normed_space ↝
_inst_13: normed_space ↝
 -/

-- analysis\calculus\iterated_deriv.lean
#print iterated_deriv /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_within /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_within_univ /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_within_eq_iterated_fderiv_within /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_within_eq_equiv_comp /- _inst_3: normed_space ↝
 -/
#print iterated_fderiv_within_eq_equiv_comp /- _inst_3: normed_space ↝
 -/
#print iterated_fderiv_within_apply_eq_iterated_deriv_within_mul_prod /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_within_zero /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_within_one /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_on_of_continuous_on_differentiable_on_deriv /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_on_of_differentiable_on_deriv /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_on.continuous_on_iterated_deriv_within /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_on.differentiable_on_iterated_deriv_within /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_on_iff_continuous_on_differentiable_on_deriv /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_within_succ /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_within_eq_iterate /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_within_succ' /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_eq_iterated_fderiv /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_eq_equiv_comp /- _inst_3: normed_space ↝
 -/
#print iterated_fderiv_eq_equiv_comp /- _inst_3: normed_space ↝
 -/
#print iterated_fderiv_apply_eq_iterated_deriv_mul_prod /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_zero /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_one /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_iff_iterated_deriv /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_of_differentiable_iterated_deriv /- _inst_3: normed_space ↝
 -/
#print times_cont_diff.continuous_iterated_deriv /- _inst_3: normed_space ↝
 -/
#print times_cont_diff.differentiable_iterated_deriv /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_succ /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_eq_iterate /- _inst_3: normed_space ↝
 -/
#print iterated_deriv_succ' /- _inst_3: normed_space ↝
 -/

-- analysis\calculus\local_extr.lean
#print pos_tangent_cone_at /- _inst_2: normed_space ↝
 -/
#print pos_tangent_cone_at_mono /- _inst_2: normed_space ↝
 -/
#print mem_pos_tangent_cone_at_of_segment_subset /- _inst_2: normed_space ↝
 -/
#print pos_tangent_cone_at_univ /- _inst_2: normed_space ↝
 -/
#print is_local_max_on.has_fderiv_within_at_nonpos /- _inst_2: normed_space ↝
 -/
#print is_local_max_on.fderiv_within_nonpos /- _inst_2: normed_space ↝
 -/
#print is_local_max_on.has_fderiv_within_at_eq_zero /- _inst_2: normed_space ↝
 -/
#print is_local_max_on.fderiv_within_eq_zero /- _inst_2: normed_space ↝
 -/
#print is_local_min_on.has_fderiv_within_at_nonneg /- _inst_2: normed_space ↝
 -/
#print is_local_min_on.fderiv_within_nonneg /- _inst_2: normed_space ↝
 -/
#print is_local_min_on.has_fderiv_within_at_eq_zero /- _inst_2: normed_space ↝
 -/
#print is_local_min_on.fderiv_within_eq_zero /- _inst_2: normed_space ↝
 -/
#print is_local_min.has_fderiv_at_eq_zero /- _inst_2: normed_space ↝
 -/
#print is_local_min.fderiv_eq_zero /- _inst_2: normed_space ↝
 -/
#print is_local_max.has_fderiv_at_eq_zero /- _inst_2: normed_space ↝
 -/
#print is_local_max.fderiv_eq_zero /- _inst_2: normed_space ↝
 -/
#print is_local_extr.has_fderiv_at_eq_zero /- _inst_2: normed_space ↝
 -/
#print is_local_extr.fderiv_eq_zero /- _inst_2: normed_space ↝
 -/

-- analysis\calculus\mean_value.lean
#print image_norm_le_of_norm_deriv_right_lt_deriv_boundary' /- _inst_2: normed_space ↝
 -/
#print image_norm_le_of_norm_deriv_right_lt_deriv_boundary /- _inst_2: normed_space ↝
 -/
#print image_norm_le_of_norm_deriv_right_le_deriv_boundary' /- _inst_2: normed_space ↝
 -/
#print image_norm_le_of_norm_deriv_right_le_deriv_boundary /- _inst_2: normed_space ↝
 -/
#print norm_image_sub_le_of_norm_deriv_right_le_segment /- _inst_2: normed_space ↝
 -/
#print norm_image_sub_le_of_norm_deriv_le_segment' /- _inst_2: normed_space ↝
 -/
#print norm_image_sub_le_of_norm_deriv_le_segment /- _inst_2: normed_space ↝
 -/
#print norm_image_sub_le_of_norm_deriv_le_segment_01' /- _inst_2: normed_space ↝
 -/
#print norm_image_sub_le_of_norm_deriv_le_segment_01 /- _inst_2: normed_space ↝
 -/
#print convex.norm_image_sub_le_of_norm_has_fderiv_within_le /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.lipschitz_on_with_of_norm_has_fderiv_within_le /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.norm_image_sub_le_of_norm_fderiv_within_le /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.lipschitz_on_with_of_norm_fderiv_within_le /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.norm_image_sub_le_of_norm_fderiv_le /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.lipschitz_on_with_of_norm_fderiv_le /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.norm_image_sub_le_of_norm_has_fderiv_within_le' /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.norm_image_sub_le_of_norm_fderiv_within_le' /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.norm_image_sub_le_of_norm_fderiv_le' /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.is_const_of_fderiv_within_eq_zero /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print is_const_of_fderiv_eq_zero /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/
#print convex.norm_image_sub_le_of_norm_has_deriv_within_le /- _inst_4: normed_space ↝
 -/
#print convex.lipschitz_on_with_of_norm_has_deriv_within_le /- _inst_4: normed_space ↝
 -/
#print convex.norm_image_sub_le_of_norm_deriv_within_le /- _inst_4: normed_space ↝
 -/
#print convex.lipschitz_on_with_of_norm_deriv_within_le /- _inst_4: normed_space ↝
 -/
#print convex.norm_image_sub_le_of_norm_deriv_le /- _inst_4: normed_space ↝
 -/
#print convex.lipschitz_on_with_of_norm_deriv_le /- _inst_4: normed_space ↝
 -/
#print domain_mvt /- _inst_2: normed_space ↝
 -/
#print strict_fderiv_of_cont_diff /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/

-- analysis\calculus\tangent_cone.lean
#print tangent_cone_at /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝ has_scalar
 -/
#print unique_diff_within_at /- _inst_3: normed_space ↝
 -/
#print unique_diff_on /- _inst_3: normed_space ↝
 -/
#print tangent_cone_univ /- _inst_3: normed_space ↝
 -/
#print tangent_cone_mono /- _inst_3: normed_space ↝
 -/
#print tangent_cone_at.lim_zero /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
 -/
#print tangent_cone_mono_nhds /- _inst_3: normed_space ↝
 -/
#print tangent_cone_congr /- _inst_3: normed_space ↝
 -/
#print tangent_cone_inter_nhds /- _inst_3: normed_space ↝
 -/
#print subset_tangent_cone_prod_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print subset_tangent_cone_prod_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print mem_tangent_cone_of_segment_subset /- _inst_7: normed_space ↝
 -/
#print unique_diff_on.unique_diff_within_at /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at_univ /- _inst_3: normed_space ↝
 -/
#print unique_diff_on_univ /- _inst_3: normed_space ↝
 -/
#print unique_diff_on_empty /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at.mono_nhds /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at.mono /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at_congr /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at_inter /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at.inter /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at_inter' /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at.inter' /- _inst_3: normed_space ↝
 -/
#print is_open.unique_diff_within_at /- _inst_3: normed_space ↝
 -/
#print unique_diff_on.inter /- _inst_3: normed_space ↝
 -/
#print is_open.unique_diff_on /- _inst_3: normed_space ↝
 -/
#print unique_diff_within_at.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print unique_diff_on.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print unique_diff_on_convex /- _inst_7: normed_space ↝
 -/

-- analysis\calculus\times_cont_diff.lean
#print formal_multilinear_series /- _inst_8: nondiscrete_normed_field ↝ normed_field
_inst_10: normed_space ↝
_inst_12: normed_space ↝
 -/
#print formal_multilinear_series.inhabited /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.module /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.shift /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.unshift /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print formal_multilinear_series.congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.zero_eq' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.of_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.continuous_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on_zero_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on_top_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on_succ_iff_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on_succ_iff_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_nat /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.of_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_iff_forall_nat_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_top /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.continuous_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.congr_of_eventually_eq' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print filter.eventually_eq.times_cont_diff_within_at_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.mono_of_mem /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.congr_nhds /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_congr_nhds /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_inter' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_inter /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.differentiable_within_at' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_succ_iff_has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.times_cont_diff_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.times_cont_diff_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.of_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_iff_forall_nat_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_top /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_all_iff_nat /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.continuous_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.congr_mono /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_of_locally_times_cont_diff_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_succ_iff_has_fderiv_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print ftaylor_series_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_zero_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_zero_eq_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_succ_apply_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_succ_eq_comp_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_succ_apply_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_succ_eq_comp_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_one_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_congr /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_inter_open /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_inter' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_inter /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.ftaylor_series_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_of_continuous_on_differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_of_differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.continuous_on_iterated_fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.differentiable_on_iterated_fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_iff_continuous_on_differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_succ_iff_fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_succ_iff_fderiv_of_open /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_top_iff_fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_top_iff_fderiv_of_open /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.fderiv_of_open /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.continuous_on_fderiv_within /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.continuous_on_fderiv_of_open /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.continuous_on_fderiv_within_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to.zero_eq' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on_univ_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to.has_ftaylor_series_up_to_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to.of_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to.continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_zero_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to.has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to.differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_succ_iff_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_univ /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at_top /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.times_cont_diff_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.times_cont_diff_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.of_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.continuous_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at_succ_iff_has_fderiv_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_univ /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_iff_times_cont_diff_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.times_cont_diff_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.times_cont_diff_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_top /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_all_iff_nat /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.times_cont_diff_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.of_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print ftaylor_series /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_zero_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_zero_eq_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_succ_apply_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_succ_eq_comp_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_univ /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print ftaylor_series_within_univ /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_succ_apply_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_succ_eq_comp_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_one_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_iff_ftaylor_series /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_iff_continuous_differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_of_differentiable_iterated_fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_succ_iff_fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_top_iff_fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.continuous_fderiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.continuous_fderiv_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print iterated_fderiv_within_zero_fun /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_zero_fun /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_of_subsingleton /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at_of_subsingleton /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_of_subsingleton /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_of_subsingleton /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.times_cont_diff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.times_cont_diff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at_snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_id /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_within_at_id /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_at_id /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_on_id /- _inst_3: normed_space ↝
 -/
#print is_bounded_bilinear_map.times_cont_diff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.continuous_linear_map_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_within_at.continuous_linear_map_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_at.continuous_linear_map_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_on.continuous_linear_map_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff.continuous_linear_map_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_times_cont_diff_within_at_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.comp_times_cont_diff_on_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.comp_continuous_linear_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_within_at.comp_continuous_linear_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_on.comp_continuous_linear_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff.comp_continuous_linear_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.times_cont_diff_within_at_comp_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_equiv.times_cont_diff_on_comp_iff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_within_at.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_on.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_at.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff.prod /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_on.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_on.comp' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff.comp_times_cont_diff_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_within_at.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_within_at.comp' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_at.comp_times_cont_diff_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_at.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff.comp_times_cont_diff_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff.comp_times_cont_diff_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_on_fderiv_within_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.times_cont_diff_fderiv_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_add /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_neg /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.sum /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.mul /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_at.mul /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_on.mul /- _inst_3: normed_space ↝
 -/
#print times_cont_diff.mul /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_within_at.div_const /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_at.div_const /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_on.div_const /- _inst_3: normed_space ↝
 -/
#print times_cont_diff.div_const /- _inst_3: normed_space ↝
 -/
#print times_cont_diff.pow /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_smul /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_on.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_diff_within_at.prod_map' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_9: normed_space ↝
_inst_11: normed_space ↝
 -/
#print times_cont_diff_within_at.prod_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_9: normed_space ↝
_inst_11: normed_space ↝
 -/
#print times_cont_diff_on.prod_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_13: normed_space ↝
_inst_15: normed_space ↝
 -/
#print times_cont_diff_at.prod_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_9: normed_space ↝
_inst_11: normed_space ↝
 -/
#print times_cont_diff_at.prod_map' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_9: normed_space ↝
_inst_11: normed_space ↝
 -/
#print times_cont_diff.prod_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_9: normed_space ↝
_inst_11: normed_space ↝
 -/
#print times_cont_diff_at_inv /- _inst_10: normed_field ↝ division_ring normed_ring
 -/
#print times_cont_diff_within_at.inv /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_at.inv /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_within_at.div /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_at.div /- _inst_3: normed_space ↝
 -/
#print times_cont_diff.div /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_at_map_inverse /- _inst_3: normed_space ↝ normed_algebra
_inst_5: normed_space ↝
 -/
#print times_cont_diff_at.of_local_homeomorph /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print has_ftaylor_series_up_to_on.has_strict_fderiv_at /- _inst_9: normed_space ↝
_inst_11: normed_space ↝
 -/
#print times_cont_diff_at.has_strict_fderiv_at /- _inst_9: normed_space ↝
_inst_11: normed_space ↝
 -/
#print times_cont_diff_at.has_strict_fderiv_at' /- _inst_9: normed_space ↝
_inst_11: normed_space ↝
 -/
#print times_cont_diff.has_strict_fderiv_at /- _inst_9: normed_space ↝
_inst_11: normed_space ↝
 -/
#print times_cont_diff_on_succ_iff_deriv_within /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_on_succ_iff_deriv_of_open /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_on_top_iff_deriv_within /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_on_top_iff_deriv_of_open /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_on.deriv_within /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_on.deriv_of_open /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_on.continuous_on_deriv_within /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_on.continuous_on_deriv_of_open /- _inst_5: normed_space ↝
 -/
#print times_cont_diff_succ_iff_deriv /- _inst_5: normed_space ↝
 -/
#print formal_multilinear_series.restrict_scalars /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print has_ftaylor_series_up_to_on.restrict_scalars /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print times_cont_diff_within_at.restrict_scalars /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print times_cont_diff_on.restrict_scalars /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print times_cont_diff_at.restrict_scalars /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print times_cont_diff.restrict_scalars /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_10: normed_space ↝
_inst_11: is_scalar_tower ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/

-- analysis\complex\basic.lean
#print complex.finite_dimensional.proper /- _inst_2: normed_space ↝
 -/
#print complex.normed_space.restrict_scalars_real /- _inst_2: normed_space ↝
 -/
#print complex.continuous_linear_map.real_smul_complex /- _inst_2: normed_space ↝
_inst_4: normed_space ↝
 -/

-- analysis\convex\basic.lean
#print convex.combo_self /- _inst_5: linear_ordered_field ↝ monoid distrib
 -/
#print convex_on /- _inst_6: ordered_add_comm_monoid ↝ add_comm_monoid has_le
_inst_7: semimodule ↝
 -/
#print concave_on /- _inst_6: ordered_add_comm_monoid ↝ add_comm_monoid has_le
_inst_7: semimodule ↝
 -/
#print neg_convex_on_iff /- _inst_9: semimodule ↝
 -/
#print neg_concave_on_iff /- _inst_9: semimodule ↝
 -/
#print convex_on_const /- _inst_7: semimodule ↝
 -/
#print concave_on_const /- _inst_7: semimodule ↝
 -/
#print convex_on_iff_div /- _inst_7: semimodule ↝
 -/
#print concave_on_iff_div /- _inst_7: semimodule ↝
 -/
#print linear_order.convex_on_of_lt /- _inst_7: semimodule ↝
 -/
#print linear_order.concave_on_of_lt /- _inst_7: semimodule ↝
 -/
#print convex_on.subset /- _inst_7: semimodule ↝
 -/
#print concave_on.subset /- _inst_7: semimodule ↝
 -/
#print convex_on.add /- _inst_7: semimodule ↝
 -/
#print concave_on.add /- _inst_7: semimodule ↝
 -/
#print convex_on.smul /- _inst_7: semimodule ↝
 -/
#print concave_on.smul /- _inst_7: semimodule ↝
 -/
#print convex_on.le_on_segment' /- _inst_8: linear_ordered_add_comm_group ↝ ordered_add_comm_monoid linear_order
_inst_9: semimodule ↝
 -/
#print concave_on.le_on_segment' /- _inst_9: semimodule ↝
 -/
#print convex_on.le_on_segment /- _inst_9: semimodule ↝
 -/
#print concave_on.le_on_segment /- _inst_9: semimodule ↝
 -/
#print convex_on.convex_le /- _inst_7: semimodule ↝
 -/
#print concave_on.concave_le /- _inst_7: semimodule ↝
 -/
#print convex_on.convex_lt /- _inst_9: semimodule ↝
 -/
#print concave_on.convex_lt /- _inst_9: semimodule ↝
 -/
#print convex_on.convex_epigraph /- _inst_8: ordered_add_comm_group ↝ ordered_add_comm_monoid add_comm_group
_inst_9: semimodule ↝
 -/
#print concave_on.convex_hypograph /- _inst_9: semimodule ↝
 -/
#print convex_on_iff_convex_epigraph /- _inst_9: semimodule ↝
 -/
#print concave_on_iff_convex_hypograph /- _inst_9: semimodule ↝
 -/
#print convex_on.comp_affine_map /- _inst_7: semimodule ↝
 -/
#print concave_on.comp_affine_map /- _inst_7: semimodule ↝
 -/
#print convex_on.comp_linear_map /- _inst_7: semimodule ↝
 -/
#print concave_on.comp_linear_map /- _inst_7: semimodule ↝
 -/
#print convex_on.translate_right /- _inst_7: semimodule ↝
 -/
#print concave_on.translate_right /- _inst_7: semimodule ↝
 -/
#print convex_on.translate_left /- _inst_7: semimodule ↝
 -/
#print concave_on.translate_left /- _inst_7: semimodule ↝
 -/

-- analysis\convex\caratheodory.lean
#print caratheodory.mem_convex_hull_erase /- _inst_4: decidable_eq ↝
 -/
#print caratheodory.step /- _inst_4: decidable_eq ↝
 -/

-- analysis\convex\cone.lean
#print convex_cone.to_ordered_semimodule /- _inst_7: ordered_add_comm_group ↝ ordered_add_comm_monoid add_comm_group
_inst_8: semimodule ↝
 -/
#print convex_cone.positive_cone /- _inst_8: semimodule ↝
 -/
#print convex_cone.salient_of_positive_cone /- _inst_8: semimodule ↝
 -/
#print convex_cone.pointed_of_positive_cone /- _inst_8: semimodule ↝
 -/

-- analysis\convex\extrema.lean
#print is_min_on.of_is_local_min_on_of_convex_on_Icc /- _inst_6: linear_ordered_add_comm_group ↝ linear_order ordered_cancel_add_comm_monoid
_inst_7: semimodule ↝
 -/
#print is_min_on.of_is_local_min_on_of_convex_on /- _inst_7: semimodule ↝
 -/
#print is_max_on.of_is_local_max_on_of_concave_on /- _inst_7: semimodule ↝
 -/
#print is_min_on.of_is_local_min_of_convex_univ /- _inst_7: semimodule ↝
 -/
#print is_max_on.of_is_local_max_of_convex_univ /- _inst_7: semimodule ↝
 -/

-- analysis\convex\integral.lean
#print convex.smul_integral_mem /- _inst_3: normed_space ↝
 -/
#print convex.integral_mem /- _inst_3: normed_space ↝
 -/
#print convex_on.map_smul_integral_le /- _inst_3: normed_space ↝
 -/
#print convex_on.map_integral_le /- _inst_3: normed_space ↝
 -/

-- analysis\convex\topology.lean
#print convex.closure /- _inst_4: topological_add_group ↝ has_continuous_add
 -/
#print convex_on_dist /- _inst_2: normed_space ↝
 -/
#print convex_ball /- _inst_2: normed_space ↝
 -/
#print convex_closed_ball /- _inst_2: normed_space ↝
 -/
#print convex_hull_exists_dist_ge /- _inst_2: normed_space ↝
 -/
#print convex_hull_exists_dist_ge2 /- _inst_2: normed_space ↝
 -/
#print convex_hull_ediam /- _inst_2: normed_space ↝
 -/
#print convex_hull_diam /- _inst_2: normed_space ↝
 -/
#print bounded_convex_hull /- _inst_2: normed_space ↝
 -/
#print convex.is_path_connected /- _inst_2: normed_space ↝
 -/
#print normed_space.path_connected /- _inst_2: normed_space ↝
 -/
#print normed_space.loc_path_connected /- _inst_2: normed_space ↝
 -/

-- analysis\normed_space\add_torsor.lean
#print isometric.dist_point_reflection_self /- _inst_5: normed_space ↝
 -/
#print isometric.point_reflection_fixed_iff /- _inst_5: normed_space ↝
 -/
#print isometric.dist_point_reflection_self_real /- _inst_4: normed_space ↝
 -/
#print isometric.point_reflection_midpoint_left /- _inst_4: normed_space ↝
 -/
#print isometric.point_reflection_midpoint_right /- _inst_4: normed_space ↝
 -/
#print dist_center_homothety /- _inst_8: normed_space ↝
 -/
#print dist_homothety_center /- _inst_8: normed_space ↝
 -/
#print dist_homothety_self /- _inst_8: normed_space ↝
 -/
#print dist_self_homothety /- _inst_8: normed_space ↝
 -/
#print dist_left_midpoint /- _inst_8: normed_space ↝
 -/
#print dist_midpoint_left /- _inst_8: normed_space ↝
 -/
#print dist_midpoint_right /- _inst_8: normed_space ↝
 -/
#print dist_right_midpoint /- _inst_8: normed_space ↝
 -/
#print affine_map.of_map_midpoint /- _inst_7: normed_space ↝
_inst_8: normed_space ↝
 -/

-- analysis\normed_space\banach.lean
#print exists_approx_preimage_norm_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print exists_preimage_norm_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print open_mapping /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print linear_equiv.continuous_symm /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print linear_equiv.to_continuous_linear_equiv_of_continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print linear_equiv.coe_fn_to_continuous_linear_equiv_of_continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print linear_equiv.coe_fn_to_continuous_linear_equiv_of_continuous_symm /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.of_bijective /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.coe_fn_of_bijective /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.of_bijective_symm_apply_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.of_bijective_apply_symm_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/

-- analysis\normed_space\basic.lean
#print eventually_ne_of_tendsto_norm_at_top /- _inst_1: normed_group ↝ has_norm
 -/
#print normed_top_monoid /- _inst_1: normed_group ↝ has_continuous_add topological_space has_add
 -/
#print normed_top_group /- _inst_1: normed_group ↝ add_group topological_space topological_add_group
 -/
#print finset.norm_prod_le' /- _inst_2: normed_comm_ring ↝ comm_monoid normed_ring
 -/
#print finset.norm_prod_le /- _inst_2: normed_comm_ring ↝ comm_monoid normed_ring
 -/
#print units.norm_pos /- _inst_1: normed_ring ↝ monoid_with_zero normed_group
 -/
#print normed_top_ring /- _inst_1: normed_ring ↝ normed_group ring has_continuous_mul
 -/
#print normed_field.nhds_within_is_unit_ne_bot /- _inst_1: nondiscrete_normed_field ↝ group_with_zero topological_space filter.ne_bot
 -/
#print norm_smul /- _inst_3: normed_space ↝
 -/
#print dist_smul /- _inst_3: normed_space ↝
 -/
#print nnnorm_smul /- _inst_3: normed_space ↝
 -/
#print nndist_smul /- _inst_3: normed_space ↝
 -/
#print norm_smul_of_nonneg /- _inst_3: normed_space ↝
 -/
#print normed_space.topological_vector_space /- _inst_4: normed_space ↝
 -/
#print closure_ball /- _inst_7: normed_space ↝
 -/
#print frontier_ball /- _inst_7: normed_space ↝
 -/
#print interior_closed_ball /- _inst_7: normed_space ↝
 -/
#print interior_closed_ball' /- _inst_7: normed_space ↝
 -/
#print frontier_closed_ball /- _inst_7: normed_space ↝
 -/
#print frontier_closed_ball' /- _inst_7: normed_space ↝
 -/
#print rescale_to_shell /- _inst_4: normed_space ↝
 -/
#print prod.normed_space /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print submodule.normed_space /- _inst_9: normed_space ↝
 -/
#print normed_space.restrict_scalars /- _inst_5: normed_space ↝
 -/
#print semimodule.restrict_scalars.normed_space_orig /- I: normed_space ↝
 -/
#print restrict_scalars.normed_space /- _inst_5: normed_space ↝
 -/

-- analysis\normed_space\bounded_linear_maps.lean
#print is_linear_map.with_bound /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.is_bounded_linear_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.to_linear_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.to_continuous_linear_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.id /- _inst_3: normed_space ↝
 -/
#print is_bounded_linear_map.fst /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.snd /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.smul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.neg /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_linear_map.tendsto /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.lim_zero_bounded_linear_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.is_O_id /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map.is_O_comp /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_linear_map.is_O_sub /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_linear_map_prod_iso /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_linear_map_prod_multilinear /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: decidable_eq ↝
 -/
#print is_bounded_linear_map_continuous_multilinear_map_comp_linear /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: decidable_eq ↝
 -/
#print is_bounded_bilinear_map.is_O /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.is_O_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.is_O' /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.map_sub_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.map_sub_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.is_bounded_linear_map_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.is_bounded_linear_map_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map_smul /- _inst_3: normed_space ↝
 -/
#print is_bounded_bilinear_map_smul_algebra /- _inst_9: normed_algebra ↝ algebra
_inst_11: normed_space ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print is_bounded_bilinear_map_comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.is_bounded_linear_map_comp_left /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.is_bounded_linear_map_comp_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_bilinear_map_smul_right /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_bounded_bilinear_map_comp_multilinear /- _inst_5: normed_space ↝
_inst_7: normed_space ↝
_inst_8: decidable_eq ↝
 -/
#print is_bounded_bilinear_map.linear_deriv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.deriv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map_deriv_coe /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print is_bounded_bilinear_map.is_bounded_linear_map_deriv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/

-- analysis\normed_space\complemented.lean
#print continuous_linear_map.ker_closed_complemented_of_finite_dimensional_range /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.equiv_prod_of_surjective_of_is_compl /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.coe_equiv_prod_of_surjective_of_is_compl /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.equiv_prod_of_surjective_of_is_compl_to_linear_equiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.equiv_prod_of_surjective_of_is_compl_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print subspace.prod_equiv_of_closed_compl /- _inst_3: normed_space ↝
 -/
#print subspace.linear_proj_of_closed_compl /- _inst_3: normed_space ↝
 -/
#print subspace.coe_prod_equiv_of_closed_compl /- _inst_3: normed_space ↝
 -/
#print subspace.coe_prod_equiv_of_closed_compl_symm /- _inst_3: normed_space ↝
 -/
#print subspace.coe_continuous_linear_proj_of_closed_compl /- _inst_3: normed_space ↝
 -/
#print subspace.coe_continuous_linear_proj_of_closed_compl' /- _inst_3: normed_space ↝
 -/
#print subspace.closed_complemented_of_closed_compl /- _inst_3: normed_space ↝
 -/
#print subspace.closed_complemented_iff_has_closed_compl /- _inst_3: normed_space ↝
 -/
#print subspace.closed_complemented_of_quotient_finite_dimensional /- _inst_3: normed_space ↝
 -/

-- analysis\normed_space\dual.lean
#print normed_space.dual /- _inst_1: nondiscrete_normed_field ↝ normed_field
_inst_3: normed_space ↝
 -/
#print normed_space.dual.inhabited /- _inst_3: normed_space ↝
 -/
#print normed_space.inclusion_in_double_dual' /- _inst_3: normed_space ↝
 -/
#print normed_space.dual_def /- _inst_3: normed_space ↝
 -/
#print normed_space.double_dual_bound /- _inst_3: normed_space ↝
 -/
#print normed_space.inclusion_in_double_dual /- _inst_3: normed_space ↝
 -/
#print normed_space.norm_le_dual_bound /- _inst_3: normed_space ↝
 -/
#print normed_space.inclusion_in_double_dual_isometry /- _inst_3: normed_space ↝
 -/

-- analysis\normed_space\enorm.lean
#print enorm.map_smul /- _inst_3: vector_space ↝
 -/
#print enorm.finite_subspace.normed_space /- _inst_3: vector_space ↝
 -/

-- analysis\normed_space\extend.lean
#print linear_map.extend_to_𝕜 /- _inst_3: normed_space ↝
 -/
#print norm_bound /- _inst_3: normed_space ↝
 -/
#print continuous_linear_map.extend_to_𝕜 /- _inst_3: normed_space ↝
 -/

-- analysis\normed_space\finite_dimension.lean
#print linear_map.continuous_on_pi /- _inst_2: normed_field ↝ field topological_space
_inst_6: topological_add_group ↝ has_continuous_add
 -/
#print continuous_equiv_fun_basis /- _inst_3: normed_space ↝
 -/
#print linear_map.continuous_of_finite_dimensional /- _inst_3: normed_space ↝
 -/
#print linear_map.to_continuous_linear_map /- _inst_3: normed_space ↝
 -/
#print linear_equiv.to_continuous_linear_equiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_basis.constrL /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_basis.coe_constrL /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_basis.equiv_funL /- _inst_3: normed_space ↝
 -/
#print is_basis.constrL_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_basis.constrL_basis /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print is_basis.sup_norm_le_norm /- _inst_3: normed_space ↝
 -/
#print is_basis.op_norm_le /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.topological_space.second_countable_topology /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_14: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/
#print finite_dimensional.complete /- _inst_3: normed_space ↝
 -/
#print submodule.complete_of_finite_dimensional /- _inst_3: normed_space ↝
 -/
#print submodule.closed_of_finite_dimensional /- _inst_3: normed_space ↝
 -/
#print continuous_linear_map.exists_right_inverse_of_surjective /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print closed_embedding_smul_left /- _inst_3: normed_space ↝
 -/
#print is_closed_map_smul_left /- _inst_3: normed_space ↝
 -/
#print finite_dimensional.proper /- _inst_3: normed_space ↝
 -/
#print finite_dimensional.proper_real /- _inst_2: normed_space ↝
 -/
#print summable_norm_iff /- _inst_2: normed_space ↝ complete_space
 -/

-- analysis\normed_space\hahn_banach.lean
#print norm' /- _inst_1: nondiscrete_normed_field ↝ normed_ring
_inst_3: normed_group ↝ has_norm
 -/
#print real.exists_extension_norm_eq /- _inst_2: normed_space ↝
 -/
#print exists_extension_norm_eq /- _inst_3: normed_space ↝
 -/
#print coord_norm' /- _inst_3: normed_space ↝
 -/
#print exists_dual_vector /- _inst_3: normed_space ↝
 -/
#print exists_dual_vector' /- _inst_3: normed_space ↝
 -/

-- analysis\normed_space\inner_product.lean
#print inner_product_space.of_core.to_has_inner /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.norm_sq /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_conj_sym /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_self_nonneg /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_self_nonneg_im /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_self_im_zero /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_add_left /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_add_right /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_norm_sq_eq_inner_self /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_re_symm /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_im_symm /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_smul_left /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_smul_right /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_zero_left /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_zero_right /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_self_eq_zero /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_self_re_to_K /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_abs_conj_sym /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_neg_left /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_neg_right /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_sub_left /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_sub_right /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_mul_conj_re_abs /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_add_add_self /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_sub_sub_self /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_mul_inner_self_le /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.to_has_norm /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.norm_eq_sqrt_inner /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.inner_self_eq_norm_square /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.sqrt_norm_sq_eq_norm /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.abs_inner_le_norm /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.to_normed_group /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core.to_normed_space /- _inst_3: semimodule ↝
 -/
#print inner_product_space.of_core /- _inst_3: semimodule ↝
 -/
#print euclidean_space /- _inst_4: is_R_or_C ↝
_inst_5: fintype ↝
 -/
#print has_inner.is_R_or_C_to_real /- _inst_2: inner_product_space ↝ has_inner
 -/
#print is_bounded_bilinear_map_inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
 -/
#print times_cont_diff_inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
 -/
#print times_cont_diff_at_inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
 -/
#print differentiable_inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
 -/
#print continuous_inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
 -/
#print times_cont_diff_within_at.inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_at.inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_on.inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff.inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
_inst_7: normed_space ↝
 -/
#print differentiable_within_at.inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
_inst_7: normed_space ↝
 -/
#print differentiable_at.inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
_inst_7: normed_space ↝
 -/
#print differentiable_on.inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
_inst_7: normed_space ↝
 -/
#print differentiable.inner /- _inst_4: normed_space ↝
_inst_5: is_scalar_tower ↝
_inst_7: normed_space ↝
 -/

-- analysis\normed_space\mazur_ulam.lean
#print isometric.midpoint_fixed /- _inst_2: normed_space ↝
 -/
#print isometric.map_midpoint /- _inst_2: normed_space ↝
_inst_6: normed_space ↝
 -/
#print isometric.to_real_linear_equiv_of_map_zero /- _inst_2: normed_space ↝
_inst_6: normed_space ↝
 -/
#print isometric.coe_to_real_linear_equiv_of_map_zero /- _inst_2: normed_space ↝
_inst_6: normed_space ↝
 -/
#print isometric.coe_to_real_linear_equiv_of_map_zero_symm /- _inst_2: normed_space ↝
_inst_6: normed_space ↝
 -/
#print isometric.to_real_linear_equiv /- _inst_2: normed_space ↝
_inst_6: normed_space ↝
 -/
#print isometric.to_real_linear_equiv_apply /- _inst_2: normed_space ↝
_inst_6: normed_space ↝
 -/
#print isometric.to_real_linear_equiv_symm_apply /- _inst_2: normed_space ↝
_inst_6: normed_space ↝
 -/
#print isometric.to_affine_equiv /- _inst_2: normed_space ↝
_inst_6: normed_space ↝
 -/
#print isometric.coe_to_affine_equiv /- _inst_2: normed_space ↝
_inst_6: normed_space ↝
 -/

-- analysis\normed_space\multilinear.lean
#print multilinear_map.exists_bound_of_continuous /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print multilinear_map.norm_image_sub_le_of_bound' /- _inst_1: decidable_eq ↝
_inst_3: nondiscrete_normed_field ↝ normed_field
_inst_11: normed_space ↝
 -/
#print multilinear_map.norm_image_sub_le_of_bound /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print multilinear_map.continuous_of_bound /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print multilinear_map.mk_continuous /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print multilinear_map.restr_norm_le /- _inst_3: nondiscrete_normed_field ↝ normed_field
_inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.bound /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.op_norm /- _inst_1: decidable_eq ↝
_inst_3: nondiscrete_normed_field ↝ normed_field
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.has_op_norm /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.norm_def /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.bounds_nonempty /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.bounds_bdd_below /- _inst_1: decidable_eq ↝
_inst_3: nondiscrete_normed_field ↝ normed_field
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.op_norm_nonneg /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.le_op_norm /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.ratio_le_op_norm /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.unit_le_op_norm /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.op_norm_le_bound /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.op_norm_add_le /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.op_norm_zero_iff /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.op_norm_smul_le /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
_inst_12: nondiscrete_normed_field ↝ normed_field
_inst_13: normed_algebra ↝ algebra
_inst_14: normed_space ↝
_inst_15: is_scalar_tower ↝
 -/
#print continuous_multilinear_map.op_norm_neg /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.to_normed_group /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.to_normed_space /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
_inst_14: normed_space ↝
_inst_15: is_scalar_tower ↝
 -/
#print continuous_multilinear_map.norm_restrict_scalars /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
_inst_13: normed_algebra ↝ has_scalar
_inst_14: normed_space ↝
_inst_15: is_scalar_tower ↝
 -/
#print continuous_multilinear_map.restrict_scalars_linear /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
_inst_14: normed_space ↝
_inst_15: is_scalar_tower ↝
 -/
#print continuous_multilinear_map.continuous_restrict_scalars /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
_inst_14: normed_space ↝
_inst_15: is_scalar_tower ↝
 -/
#print continuous_multilinear_map.norm_image_sub_le_of_bound' /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.norm_image_sub_le_of_bound /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.continuous_eval /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.continuous_eval_left /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.has_sum_eval /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.complete_space /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print multilinear_map.mk_continuous_norm_le /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.restr /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.norm_restr /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.mk_pi_algebra /- _inst_1: decidable_eq ↝
 -/
#print continuous_multilinear_map.mk_pi_algebra_apply /- _inst_1: decidable_eq ↝
 -/
#print continuous_multilinear_map.norm_mk_pi_algebra_le /- _inst_1: decidable_eq ↝
 -/
#print continuous_multilinear_map.norm_mk_pi_algebra_of_empty /- _inst_1: decidable_eq ↝
 -/
#print continuous_multilinear_map.norm_mk_pi_algebra /- _inst_1: decidable_eq ↝
 -/
#print continuous_multilinear_map.mk_pi_field /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.mk_pi_field_apply /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.mk_pi_field_apply_one_eq_self /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.pi_field_equiv_aux /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.pi_field_equiv /- _inst_1: decidable_eq ↝
_inst_11: normed_space ↝
 -/
#print continuous_linear_map.norm_map_tail_le /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.norm_map_init_le /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.norm_map_cons_le /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.norm_map_snoc_le /- _inst_11: normed_space ↝
 -/
#print continuous_linear_map.uncurry_left /- _inst_11: normed_space ↝
 -/
#print continuous_linear_map.uncurry_left_apply /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry_left /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry_left_apply /- _inst_11: normed_space ↝
 -/
#print continuous_linear_map.curry_uncurry_left /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.uncurry_curry_left /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry_left_norm /- _inst_11: normed_space ↝
 -/
#print continuous_linear_map.uncurry_left_norm /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_left_equiv_aux /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_left_equiv /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_left_equiv_apply /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_left_equiv_symm_apply /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.uncurry_right /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.uncurry_right_apply /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry_right /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry_right_apply /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry_uncurry_right /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.uncurry_curry_right /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry_right_norm /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.uncurry_right_norm /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_right_equiv_aux /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_right_equiv /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_right_equiv_apply /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_right_equiv_symm_apply /- _inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.uncurry0 /- _inst_3: nondiscrete_normed_field ↝ normed_field
_inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry0 /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry0_apply /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.uncurry0_apply /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.apply_zero_curry0 /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.uncurry0_curry0 /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry0_uncurry0 /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.uncurry0_norm /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.fin0_apply_norm /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_map.curry0_norm /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_fin0_aux /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_fin0 /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_fin0_apply /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_fin0_symm_apply /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_fin1 /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_fin1_apply /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/
#print continuous_multilinear_curry_fin1_symm_apply /- _inst_8: normed_space ↝
_inst_11: normed_space ↝
 -/

-- analysis\normed_space\operator_norm.lean
#print exists_pos_bound_of_bound /- _inst_2: normed_group ↝ has_norm
 -/
#print linear_map.lipschitz_of_bound /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.antilipschitz_of_bound /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.uniform_continuous_of_bound /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.continuous_of_bound /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.mk_continuous /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.to_continuous_linear_map₁ /- _inst_5: normed_space ↝
 -/
#print linear_map.mk_continuous_of_exists_bound /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_of_linear_of_bound /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.mk_continuous_coe /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.mk_continuous_apply /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.mk_continuous_of_exists_bound_coe /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.mk_continuous_of_exists_bound_apply /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.to_continuous_linear_map₁_coe /- _inst_5: normed_space ↝
 -/
#print linear_map.to_continuous_linear_map₁_apply /- _inst_5: normed_space ↝
 -/
#print linear_map.continuous_iff_is_closed_ker /- _inst_5: normed_space ↝
 -/
#print linear_map.bound_of_shell /- _inst_4: nondiscrete_normed_field ↝ normed_field
_inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_map.bound_of_continuous /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.bound /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.is_O_id /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.is_O_comp /- _inst_6: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.is_O_sub /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.of_homothety /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.to_span_singleton_homothety /- _inst_4: nondiscrete_normed_field ↝ normed_field
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.to_span_singleton /- _inst_5: normed_space ↝
 -/
#print continuous_linear_map.op_norm /- _inst_4: nondiscrete_normed_field ↝ normed_field
_inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.has_op_norm /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.norm_def /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.bounds_nonempty /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.bounds_bdd_below /- _inst_4: nondiscrete_normed_field ↝ normed_field
_inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_nonneg /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.le_op_norm /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.le_op_norm_of_le /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.le_of_op_norm_le /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.lipschitz /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.ratio_le_op_norm /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.unit_le_op_norm /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_le_bound /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_le_of_lipschitz /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_le_of_shell /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_le_of_ball /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_le_of_shell' /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_eq_of_bounds /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_add_le /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_zero_iff /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.norm_id_le /- _inst_5: normed_space ↝
 -/
#print continuous_linear_map.norm_id /- _inst_5: normed_space ↝
 -/
#print continuous_linear_map.op_norm_smul_le /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_neg /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.to_normed_group /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.to_normed_space /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.op_norm_comp_le /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.to_normed_ring /- _inst_5: normed_space ↝
 -/
#print continuous_linear_map.to_normed_algebra /- _inst_5: normed_space ↝ algebra
 -/
#print continuous_linear_map.uniform_continuous /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.isometry_iff_norm_image_eq_norm /- _inst_4: nondiscrete_normed_field ↝ normed_field
_inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.homothety_norm /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.to_span_singleton_norm /- _inst_5: normed_space ↝
 -/
#print continuous_linear_map.uniform_embedding_of_bound /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.antilipschitz_of_uniform_embedding /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.complete_space /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.extend /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.extend_unique /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.extend_zero /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: normed_space ↝
 -/
#print continuous_linear_map.op_norm_extend_le /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
_inst_7: normed_space ↝
 -/
#print linear_map.mk_continuous_norm_le /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.norm_smul_right_apply /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.smul_rightL /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.norm_smul_rightL_apply /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.norm_smul_rightL /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.applyₗ /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.continuous_applyₗ /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.apply /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.restrict_scalars /- _inst_11: normed_space ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
_inst_15: normed_space ↝
_inst_16: normed_space ↝
_inst_17: is_scalar_tower ↝
 -/
#print continuous_linear_map.restrict_scalars_coe_eq_coe /- _inst_11: normed_space ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
_inst_15: normed_space ↝
_inst_16: normed_space ↝
_inst_17: is_scalar_tower ↝
 -/
#print continuous_linear_map.restrict_scalars_coe_eq_coe' /- _inst_11: normed_space ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
_inst_15: normed_space ↝
_inst_16: normed_space ↝
_inst_17: is_scalar_tower ↝
 -/
#print continuous_linear_map.has_scalar_extend_scalars /- _inst_5: normed_space ↝
_inst_11: normed_space ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print continuous_linear_map.module_extend_scalars /- _inst_5: normed_space ↝
_inst_11: normed_space ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print continuous_linear_map.normed_space_extend_scalars /- _inst_5: normed_space ↝
_inst_11: normed_space ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print continuous_linear_map.smul_algebra_right /- _inst_5: normed_space ↝
_inst_11: normed_space ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print continuous_linear_map.smul_algebra_right_apply /- _inst_5: normed_space ↝
_inst_11: normed_space ↝
_inst_12: normed_space ↝
_inst_13: is_scalar_tower ↝
 -/
#print continuous_linear_map.has_sum /- _inst_10: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.summable /- _inst_10: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_equiv.has_sum /- _inst_10: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_equiv.summable /- _inst_10: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_equiv.lipschitz /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.antilipschitz /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.is_O_comp /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.is_O_sub /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.is_O_comp_rev /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.is_O_sub_rev /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.uniform_embedding /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.one_le_norm_mul_norm_symm /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.norm_pos /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.norm_symm_pos /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.subsingleton_or_norm_symm_pos /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.subsingleton_or_nnnorm_symm_pos /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.homothety_inverse /- _inst_4: nondiscrete_normed_field ↝ normed_field
_inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.of_homothety /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_equiv.to_span_nonzero_singleton_homothety /- _inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.to_span_nonzero_singleton /- _inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.coord /- _inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.coord_norm /- _inst_5: normed_space ↝
 -/
#print continuous_linear_equiv.coord_self /- _inst_5: normed_space ↝
 -/
#print linear_equiv.uniform_embedding /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/
#print linear_equiv.to_continuous_linear_equiv_of_bounds /- _inst_5: normed_space ↝
_inst_6: normed_space ↝
 -/

-- analysis\normed_space\riesz_lemma.lean
#print riesz_lemma /- _inst_3: normed_space ↝
 -/

-- analysis\seminorm.lean
#print absorbs /- _inst_1: nondiscrete_normed_field ↝ field has_norm
_inst_3: vector_space ↝ has_scalar
 -/
#print absorbent /- _inst_1: nondiscrete_normed_field ↝ field has_norm
_inst_3: vector_space ↝ has_scalar
 -/
#print balanced /- _inst_1: nondiscrete_normed_field ↝ field has_norm
_inst_3: vector_space ↝ has_scalar
 -/
#print balanced.absorbs_self /- _inst_3: vector_space ↝
 -/
#print absorbent_nhds_zero /- _inst_3: vector_space ↝
 -/
#print balanced_zero_union_interior /- _inst_3: vector_space ↝
 -/
#print seminorm.has_coe_to_fun /- _inst_1: nondiscrete_normed_field ↝ normed_field
 -/

-- analysis\special_functions\exp_log.lean
#print has_fderiv_within_at.cexp /- _inst_2: normed_space ↝
 -/
#print has_fderiv_at.cexp /- _inst_2: normed_space ↝
 -/
#print differentiable_within_at.cexp /- _inst_2: normed_space ↝
 -/
#print differentiable_at.cexp /- _inst_2: normed_space ↝
 -/
#print differentiable_on.cexp /- _inst_2: normed_space ↝
 -/
#print differentiable.cexp /- _inst_2: normed_space ↝
 -/
#print times_cont_diff.cexp /- _inst_2: normed_space ↝
 -/
#print times_cont_diff_at.cexp /- _inst_2: normed_space ↝
 -/
#print times_cont_diff_on.cexp /- _inst_2: normed_space ↝
 -/
#print times_cont_diff_within_at.cexp /- _inst_2: normed_space ↝
 -/
#print times_cont_diff.exp /- _inst_2: normed_space ↝
 -/
#print times_cont_diff_at.exp /- _inst_2: normed_space ↝
 -/
#print times_cont_diff_on.exp /- _inst_2: normed_space ↝
 -/
#print times_cont_diff_within_at.exp /- _inst_2: normed_space ↝
 -/
#print has_fderiv_within_at.exp /- _inst_2: normed_space ↝
 -/
#print has_fderiv_at.exp /- _inst_2: normed_space ↝
 -/
#print differentiable_within_at.exp /- _inst_2: normed_space ↝
 -/
#print differentiable_at.exp /- _inst_2: normed_space ↝
 -/
#print differentiable_on.exp /- _inst_2: normed_space ↝
 -/
#print differentiable.exp /- _inst_2: normed_space ↝
 -/
#print fderiv_within_exp /- _inst_2: normed_space ↝
 -/
#print fderiv_exp /- _inst_2: normed_space ↝
 -/

-- analysis\specific_limits.lean
#print tendsto_pow_at_top_at_top_of_one_lt /- _inst_1: linear_ordered_ring ↝ ordered_add_comm_group linear_ordered_semiring
 -/

-- category_theory\abelian\basic.lean
#print category_theory.abelian.has_finite_biproducts /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_finite_products category_theory.preadditive
 -/
#print category_theory.abelian.has_pullbacks /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_finite_products category_theory.preadditive category_theory.limits.has_kernels
 -/
#print category_theory.abelian.has_pushouts /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_cokernels category_theory.limits.has_binary_coproducts category_theory.limits.has_finite_products category_theory.preadditive
 -/

-- category_theory\abelian\non_preadditive.lean
#print category_theory.non_preadditive_abelian.epi_is_cokernel_of_kernel /- _inst_3: category_theory.epi ↝ category_theory.is_iso
 -/
#print category_theory.non_preadditive_abelian.mono_is_kernel_of_cokernel /- _inst_3: category_theory.mono ↝ category_theory.is_iso
 -/
#print category_theory.non_preadditive_abelian.mono_Δ /- _inst_2: category_theory.non_preadditive_abelian ↝ category_theory.limits.has_finite_products
 -/
#print category_theory.non_preadditive_abelian.lift_map /- _inst_2: category_theory.non_preadditive_abelian ↝ category_theory.limits.has_zero_morphisms category_theory.limits.has_finite_products
 -/

-- category_theory\action.lean
#print category_theory.action_as_functor_map /- _inst_2: mul_action ↝
 -/
#print category_theory.action_as_functor_obj /- _inst_2: mul_action ↝
 -/
#print category_theory.action_as_functor /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category.category_theory.groupoid /- _inst_4: mul_action ↝
 -/
#print category_theory.action_category.π /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category.π_map /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category.π_obj /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category.obj_equiv /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category.hom_as_subtype /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category.inhabited /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category.stabilizer_iso_End /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category.stabilizer_iso_End_apply /- _inst_2: mul_action ↝
 -/
#print category_theory.action_category.stabilizer_iso_End_symm_apply /- _inst_2: mul_action ↝
 -/

-- category_theory\adjunction\limits.lean
#print category_theory.adjunction.has_colimit_comp_equivalence /- _inst_4: category_theory.is_equivalence ↝ category_theory.limits.preserves_colimit
 -/
#print category_theory.adjunction.has_limit_comp_equivalence /- _inst_4: category_theory.is_equivalence ↝ category_theory.limits.preserves_limit
 -/

-- category_theory\category\Kleisli.lean
#print category_theory.Kleisli /- _inst_1: monad ↝
 -/
#print category_theory.Kleisli.id_def /- _inst_2: is_lawful_monad ↝
 -/
#print category_theory.Kleisli.comp_def /- _inst_2: is_lawful_monad ↝
 -/

-- category_theory\category\default.lean
#print category_theory.eq_whisker /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#print category_theory.whisker_eq /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#print category_theory.comp_dite /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#print category_theory.dite_comp /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#print category_theory.hom_of_le /- _inst_1: preorder ↝ category_theory.has_hom has_le
 -/
#print category_theory.le_of_hom /- _inst_1: preorder ↝ category_theory.has_hom has_le
 -/

-- category_theory\concrete_category\bundled_hom.lean
#print category_theory.bundled_hom.bundled_hom_of_parent_projection /- _inst_1: category_theory.bundled_hom.parent_projection ↝
 -/

-- category_theory\core.lean
#print category_theory.core.forget_functor_to_core /- _inst_2: category_theory.groupoid ↝ category_theory.category
 -/

-- category_theory\endomorphism.lean
#print category_theory.End /- _inst_1: category_theory.category_struct ↝ category_theory.has_hom
 -/

-- category_theory\filtered.lean
#print category_theory.is_filtered_of_semilattice_sup_top /- _inst_2: semilattice_sup_top ↝ category_theory.small_category has_top category_theory.is_filtered_or_empty
 -/

-- category_theory\fin_category.lean
#print category_theory.discrete_hom_fintype /- _inst_1: decidable_eq ↝
 -/
#print category_theory.fin_category_discrete_of_decidable_fintype /- _inst_1: decidable_eq ↝
 -/

-- category_theory\full_subcategory.lean
#print category_theory.induced_category /- _inst_1: category_theory.category ↝
 -/

-- category_theory\graded_object.lean
#print category_theory.graded_object_with_shift /- _inst_1: add_comm_group ↝
 -/

-- category_theory\is_connected.lean
#print category_theory.is_connected_of_equivalent /- _inst_4: category_theory.is_connected ↝ nonempty category_theory.is_preconnected
 -/
#print category_theory.zag /- _inst_1: category_theory.category ↝ category_theory.has_hom
 -/
#print category_theory.equiv_relation /- _inst_3: category_theory.is_connected ↝ nonempty category_theory.is_preconnected
 -/

-- category_theory\limits\cofinal.lean
#print category_theory.cofinal.colimit_iso /- _inst_3: category_theory.cofinal ↝ category_theory.limits.has_colimit category_theory.is_iso
 -/
#print category_theory.cofinal.cofinal_of_colimit_comp_coyoneda_iso_punit /- _inst_3: category_theory.cofinal ↝ category_theory.limits.has_colimit
 -/

-- category_theory\limits\creates.lean
#print category_theory.has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit
_inst_5: category_theory.creates_limits_of_shape ↝ category_theory.creates_limit
 -/
#print category_theory.has_limits_of_has_limits_creates_limits /- _inst_4: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
_inst_5: category_theory.creates_limits ↝ category_theory.creates_limits_of_shape
 -/
#print category_theory.has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape /- _inst_4: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit
_inst_5: category_theory.creates_colimits_of_shape ↝ category_theory.creates_colimit
 -/
#print category_theory.has_colimits_of_has_colimits_creates_colimits /- _inst_4: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
_inst_5: category_theory.creates_colimits ↝ category_theory.creates_colimits_of_shape
 -/
#print category_theory.preserves_limit_of_shape_of_creates_limits_of_shape_and_has_limits_of_shape /- _inst_4: category_theory.creates_limits_of_shape ↝ category_theory.limits.preserves_limit
 -/
#print category_theory.preserves_limits_of_creates_limits_and_has_limits /- _inst_4: category_theory.creates_limits ↝ category_theory.limits.preserves_limits_of_shape
_inst_5: category_theory.limits.has_limits ↝ category_theory.limits.preserves_limits_of_shape
 -/
#print category_theory.preserves_colimit_of_shape_of_creates_colimits_of_shape_and_has_colimits_of_shape /- _inst_4: category_theory.creates_colimits_of_shape ↝ category_theory.limits.preserves_colimit
 -/
#print category_theory.preserves_colimits_of_creates_colimits_and_has_colimits /- _inst_4: category_theory.creates_colimits ↝ category_theory.limits.preserves_colimits_of_shape
_inst_5: category_theory.limits.has_colimits ↝ category_theory.limits.preserves_colimits_of_shape
 -/
#print category_theory.creates_limits_of_shape_of_nat_iso /- _inst_4: category_theory.creates_limits_of_shape ↝ category_theory.creates_limit
 -/
#print category_theory.creates_limits_of_nat_iso /- _inst_4: category_theory.creates_limits ↝ category_theory.creates_limits_of_shape
 -/
#print category_theory.creates_colimits_of_shape_of_nat_iso /- _inst_4: category_theory.creates_colimits_of_shape ↝ category_theory.creates_colimit
 -/
#print category_theory.creates_colimits_of_nat_iso /- _inst_4: category_theory.creates_colimits ↝ category_theory.creates_colimits_of_shape
 -/
#print category_theory.comp_creates_limits_of_shape /- _inst_4: category_theory.creates_limits_of_shape ↝ category_theory.creates_limit
_inst_5: category_theory.creates_limits_of_shape ↝ category_theory.creates_limit
 -/
#print category_theory.comp_creates_limits /- _inst_4: category_theory.creates_limits ↝ category_theory.creates_limits_of_shape
_inst_5: category_theory.creates_limits ↝ category_theory.creates_limits_of_shape
 -/
#print category_theory.comp_creates_colimits_of_shape /- _inst_4: category_theory.creates_colimits_of_shape ↝ category_theory.creates_colimit
_inst_5: category_theory.creates_colimits_of_shape ↝ category_theory.creates_colimit
 -/
#print category_theory.comp_creates_colimits /- _inst_4: category_theory.creates_colimits ↝ category_theory.creates_colimits_of_shape
_inst_5: category_theory.creates_colimits ↝ category_theory.creates_colimits_of_shape
 -/

-- category_theory\limits\functor_category.lean
#print category_theory.limits.functor_category_has_limits_of_shape /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit
 -/
#print category_theory.limits.functor_category_has_colimits_of_shape /- _inst_4: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit
 -/
#print category_theory.limits.functor_category_has_limits /- _inst_4: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#print category_theory.limits.functor_category_has_colimits /- _inst_4: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#print category_theory.limits.evaluation_preserves_limits /- _inst_4: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#print category_theory.limits.evaluation_preserves_colimits /- _inst_4: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/

-- category_theory\limits\limits.lean
#print category_theory.limits.limit.map_pre' /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit
 -/
#print category_theory.limits.limit.map_post /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit
_inst_6: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit
 -/
#print category_theory.limits.has_limits_of_shape_of_equivalence /- _inst_5: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit
 -/
#print category_theory.limits.colimit.pre_map' /- _inst_4: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit
 -/
#print category_theory.limits.has_colimits_of_shape_of_equivalence /- _inst_5: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit
 -/

-- category_theory\limits\over.lean
#print category_theory.over.has_colimits_of_shape /- _inst_3: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit
 -/
#print category_theory.over.has_colimits /- _inst_3: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#print category_theory.over.forget_preserves_colimits /- _inst_3: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#print category_theory.under.has_limits_of_shape /- _inst_3: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit
 -/
#print category_theory.under.has_limits /- _inst_3: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/

-- category_theory\limits\preserves\basic.lean
#print category_theory.limits.comp_preserves_limits_of_shape /- _inst_4: category_theory.limits.preserves_limits_of_shape ↝ category_theory.limits.preserves_limit
_inst_5: category_theory.limits.preserves_limits_of_shape ↝ category_theory.limits.preserves_limit
 -/
#print category_theory.limits.comp_preserves_limits /- _inst_4: category_theory.limits.preserves_limits ↝ category_theory.limits.preserves_limits_of_shape
_inst_5: category_theory.limits.preserves_limits ↝ category_theory.limits.preserves_limits_of_shape
 -/
#print category_theory.limits.comp_preserves_colimits_of_shape /- _inst_4: category_theory.limits.preserves_colimits_of_shape ↝ category_theory.limits.preserves_colimit
_inst_5: category_theory.limits.preserves_colimits_of_shape ↝ category_theory.limits.preserves_colimit
 -/
#print category_theory.limits.comp_preserves_colimits /- _inst_4: category_theory.limits.preserves_colimits ↝ category_theory.limits.preserves_colimits_of_shape
_inst_5: category_theory.limits.preserves_colimits ↝ category_theory.limits.preserves_colimits_of_shape
 -/
#print category_theory.limits.preserves_limits_of_shape_of_nat_iso /- _inst_4: category_theory.limits.preserves_limits_of_shape ↝ category_theory.limits.preserves_limit
 -/
#print category_theory.limits.preserves_limits_of_nat_iso /- _inst_4: category_theory.limits.preserves_limits ↝ category_theory.limits.preserves_limits_of_shape
 -/
#print category_theory.limits.preserves_colimits_of_shape_of_nat_iso /- _inst_4: category_theory.limits.preserves_colimits_of_shape ↝ category_theory.limits.preserves_colimit
 -/
#print category_theory.limits.preserves_colimits_of_nat_iso /- _inst_4: category_theory.limits.preserves_colimits ↝ category_theory.limits.preserves_colimits_of_shape
 -/
#print category_theory.limits.comp_reflects_limits_of_shape /- _inst_4: category_theory.limits.reflects_limits_of_shape ↝ category_theory.limits.reflects_limit
 -/
#print category_theory.limits.comp_reflects_limits /- _inst_4: category_theory.limits.reflects_limits ↝ category_theory.limits.reflects_limits_of_shape
_inst_5: category_theory.limits.reflects_limits ↝ category_theory.limits.reflects_limits_of_shape
 -/
#print category_theory.limits.comp_reflects_colimits_of_shape /- _inst_4: category_theory.limits.reflects_colimits_of_shape ↝ category_theory.limits.reflects_colimit
 -/
#print category_theory.limits.comp_reflects_colimits /- _inst_4: category_theory.limits.reflects_colimits ↝ category_theory.limits.reflects_colimits_of_shape
_inst_5: category_theory.limits.reflects_colimits ↝ category_theory.limits.reflects_colimits_of_shape
 -/
#print category_theory.limits.preserves_limits_of_reflects_of_preserves /- _inst_5: category_theory.limits.reflects_limits ↝ category_theory.limits.reflects_limits_of_shape
 -/
#print category_theory.limits.reflects_limits_of_shape_of_nat_iso /- _inst_4: category_theory.limits.reflects_limits_of_shape ↝ category_theory.limits.reflects_limit
 -/
#print category_theory.limits.reflects_limits_of_nat_iso /- _inst_4: category_theory.limits.reflects_limits ↝ category_theory.limits.reflects_limits_of_shape
 -/
#print category_theory.limits.preserves_colimits_of_reflects_of_preserves /- _inst_5: category_theory.limits.reflects_colimits ↝ category_theory.limits.reflects_colimits_of_shape
 -/
#print category_theory.limits.reflects_colimits_of_shape_of_nat_iso /- _inst_4: category_theory.limits.reflects_colimits_of_shape ↝ category_theory.limits.reflects_colimit
 -/
#print category_theory.limits.reflects_colimits_of_nat_iso /- _inst_4: category_theory.limits.reflects_colimits ↝ category_theory.limits.reflects_colimits_of_shape
 -/

-- category_theory\limits\preserves\functor_category.lean
#print category_theory.functor_category.prod_preserves_colimits /- _inst_4: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/

-- category_theory\limits\shapes\biproducts.lean
#print category_theory.limits.bicone_ι_π_self /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.bicone_ι_π_ne /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.bicone.to_cone /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.bicone.to_cone_X /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.bicone.to_cone_π_app /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.bicone.to_cocone_X /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.bicone.to_cocone_ι_app /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.bicone.to_cocone /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.has_biproduct.mk /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.get_biproduct_data /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.bicone /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.is_limit /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.is_colimit /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.has_product_of_has_biproduct /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.has_coproduct_of_has_biproduct /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.has_finite_products_of_has_finite_biproducts /- _inst_4: category_theory.limits.has_finite_biproducts ↝ category_theory.limits.has_biproduct
 -/
#print category_theory.limits.has_finite_coproducts_of_has_finite_biproducts /- _inst_4: category_theory.limits.has_finite_biproducts ↝ category_theory.limits.has_biproduct
 -/
#print category_theory.limits.biproduct_iso /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.π /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.bicone_π /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.bicone_ι /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_π_assoc /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_π /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_π_self /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_π_self_assoc /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_π_ne_assoc /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_π_ne /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.lift /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.desc /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.lift_π /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.lift_π_assoc /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_desc_assoc /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_desc /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.map /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.map' /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.hom_ext /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.hom_ext' /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.map_eq_map' /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_mono /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.π_epi /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.map_π_assoc /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.map_π /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_map /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.ι_map_assoc /- _inst_1: decidable_eq ↝
 -/
#print category_theory.limits.has_binary_biproducts_of_finite_biproducts /- _inst_4: category_theory.limits.has_finite_biproducts ↝ category_theory.limits.has_biproducts_of_shape
 -/
#print category_theory.limits.has_binary_products_of_has_binary_biproducts /- _inst_4: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#print category_theory.limits.has_binary_coproducts_of_has_binary_biproducts /- _inst_4: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#print category_theory.limits.biprod.symmetry' /- _inst_4: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#print category_theory.limits.has_biproduct_of_total /- _inst_3: decidable_eq ↝
 -/
#print category_theory.limits.has_biproduct.of_has_product /- _inst_3: decidable_eq ↝
 -/
#print category_theory.limits.has_biproduct.of_has_coproduct /- _inst_3: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.total /- _inst_3: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.lift_eq /- _inst_3: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.desc_eq /- _inst_3: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.lift_desc_assoc /- _inst_3: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.lift_desc /- _inst_3: decidable_eq ↝
 -/
#print category_theory.limits.biproduct.map_eq /- _inst_3: decidable_eq ↝
 -/
#print category_theory.limits.biprod.map_eq /- _inst_6: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/

-- category_theory\limits\shapes\constructions\over\connected.lean
#print category_theory.over.has_connected_limits /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit
 -/

-- category_theory\limits\shapes\finite_limits.lean
#print category_theory.limits.has_finite_limits_of_has_limits /- _inst_2: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#print category_theory.limits.has_finite_colimits_of_has_colimits /- _inst_2: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#print category_theory.limits.wide_pullback_shape.fintype_hom /- _inst_2: decidable_eq ↝
 -/
#print category_theory.limits.wide_pushout_shape.fintype_hom /- _inst_2: decidable_eq ↝
 -/
#print category_theory.limits.fin_category_wide_pullback /- _inst_2: decidable_eq ↝
 -/
#print category_theory.limits.fin_category_wide_pushout /- _inst_2: decidable_eq ↝
 -/

-- category_theory\limits\shapes\strong_epi.lean
#print category_theory.strong_epi_comp /- _inst_2: category_theory.strong_epi ↝ category_theory.arrow.has_lift category_theory.epi
_inst_3: category_theory.strong_epi ↝ category_theory.arrow.has_lift category_theory.epi
 -/

-- category_theory\limits\shapes\zero.lean
#print category_theory.limits.split_mono_sigma_ι /- _inst_2: decidable_eq ↝
 -/
#print category_theory.limits.split_epi_pi_π /- _inst_2: decidable_eq ↝
 -/

-- category_theory\monad\adjunction.lean
#print category_theory.μ_iso_of_reflective /- _inst_3: category_theory.reflective ↝ category_theory.full category_theory.faithful category_theory.is_right_adjoint category_theory.monad
 -/

-- category_theory\monad\limits.lean
#print category_theory.monad.forget_creates_colimits.lambda /- _inst_4: category_theory.limits.preserves_colimits_of_shape ↝ category_theory.limits.preserves_colimit
 -/
#print category_theory.comp_comparison_forget_has_limit /- _inst_4: category_theory.monadic_right_adjoint ↝ category_theory.is_right_adjoint category_theory.monad
 -/
#print category_theory.comp_comparison_has_limit /- _inst_4: category_theory.monadic_right_adjoint ↝ category_theory.limits.has_limit category_theory.is_right_adjoint category_theory.monad
 -/
#print category_theory.monadic_creates_limits /- _inst_4: category_theory.monadic_right_adjoint ↝ category_theory.is_equivalence category_theory.monad
 -/
#print category_theory.monadic_creates_colimits_of_shape_of_preserves_colimits_of_shape /- _inst_4: category_theory.monadic_right_adjoint ↝ category_theory.is_equivalence category_theory.monad
 -/
#print category_theory.monadic_creates_colimits_of_preserves_colimits /- _inst_5: category_theory.limits.preserves_colimits ↝ category_theory.limits.preserves_colimits_of_shape
 -/
#print category_theory.has_limits_of_reflective /- _inst_4: category_theory.limits.has_limits ↝ category_theory.limits.has_limit
_inst_5: category_theory.reflective ↝ category_theory.monadic_right_adjoint
 -/

-- category_theory\monoidal\transport.lean
#print category_theory.monoidal.transported /- _inst_2: category_theory.monoidal_category ↝
 -/

-- category_theory\preadditive\biproducts.lean
#print category_theory.biprod.column_nonzero_of_iso /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#print category_theory.biproduct.column_nonzero_of_iso' /- _inst_3: decidable_eq ↝
_inst_4: decidable_eq ↝
 -/
#print category_theory.biproduct.column_nonzero_of_iso /- _inst_3: decidable_eq ↝
_inst_4: decidable_eq ↝
 -/

-- category_theory\preadditive\default.lean
#print category_theory.preadditive.has_equalizers_of_has_kernels /- _inst_3: category_theory.limits.has_kernels ↝ category_theory.limits.has_kernel
 -/
#print category_theory.preadditive.has_coequalizers_of_has_cokernels /- _inst_3: category_theory.limits.has_cokernels ↝ category_theory.limits.has_cokernel
 -/

-- category_theory\sites\grothendieck.lean
#print category_theory.grothendieck_topology.right_ore_condition /- _inst_2: category_theory.category ↝ category_theory.category_struct
 -/

-- category_theory\sites\sieves.lean
#print category_theory.presieve /- _inst_1: category_theory.category ↝ category_theory.has_hom
 -/

-- combinatorics\adj_matrix.lean
#print simple_graph.adj_matrix /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.adj_matrix_apply /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.transpose_adj_matrix /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.adj_matrix_dot_product /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.dot_product_adj_matrix /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.adj_matrix_mul_vec_apply /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.adj_matrix_vec_mul_apply /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.adj_matrix_mul_apply /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.mul_adj_matrix_apply /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.trace_adj_matrix /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.adj_matrix_mul_self_apply_self /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.adj_matrix_mul_vec_const_apply /- _inst_3: decidable_rel ↝
 -/
#print simple_graph.adj_matrix_mul_vec_const_apply_of_regular /- _inst_3: decidable_rel ↝
 -/

-- combinatorics\colex.lean
#print colex.hom /- _inst_2: decidable_eq ↝
 -/
#print colex.sdiff_lt_sdiff_iff_lt /- _inst_2: decidable_eq ↝
 -/

-- combinatorics\pigeonhole.lean
#print finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_card_fiber_lt_of_card_lt_mul /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_le_card_fiber_of_mul_le_card_of_maps_to /- _inst_2: decidable_eq ↝
 -/
#print finset.exists_card_fiber_le_of_card_le_mul /- _inst_2: decidable_eq ↝
 -/
#print fintype.exists_lt_sum_fiber_of_nsmul_lt_sum /- _inst_2: decidable_eq ↝
 -/
#print fintype.exists_le_sum_fiber_of_nsmul_le_sum /- _inst_2: decidable_eq ↝
 -/
#print fintype.exists_sum_fiber_lt_of_sum_lt_nsmul /- _inst_2: decidable_eq ↝
 -/
#print fintype.exists_sum_fiber_le_of_sum_le_nsmul /- _inst_2: decidable_eq ↝
 -/
#print fintype.exists_lt_card_fiber_of_mul_lt_card /- _inst_2: decidable_eq ↝
 -/
#print fintype.exists_card_fiber_lt_of_card_lt_mul /- _inst_2: decidable_eq ↝
 -/
#print fintype.exists_le_card_fiber_of_mul_le_card /- _inst_2: decidable_eq ↝
 -/
#print fintype.exists_card_fiber_le_of_card_le_mul /- _inst_2: decidable_eq ↝
 -/

-- combinatorics\simple_graph.lean
#print complete_graph_adj_decidable /- _inst_1: decidable_eq ↝
 -/
#print simple_graph.edges_fintype /- _inst_1: decidable_eq ↝
_inst_3: decidable_rel ↝
 -/
#print simple_graph.edge_finset /- _inst_1: decidable_eq ↝
_inst_3: decidable_rel ↝
 -/
#print simple_graph.mem_edge_finset /- _inst_1: decidable_eq ↝
_inst_3: decidable_rel ↝
 -/
#print simple_graph.neighbor_set_fintype /- _inst_2: decidable_rel ↝
 -/
#print simple_graph.neighbor_finset_eq_filter /- _inst_2: decidable_rel ↝
 -/
#print simple_graph.complete_graph_degree /- _inst_2: decidable_eq ↝
 -/
#print simple_graph.complete_graph_is_regular /- _inst_2: decidable_eq ↝
 -/

-- computability\partrec.lean
#print partrec /- _inst_1: primcodable ↝ encodable
_inst_2: primcodable ↝ encodable
 -/

-- computability\primrec.lean
#print primrec /- _inst_1: primcodable ↝ encodable
_inst_2: primcodable ↝ encodable
 -/
#print primrec.eq /- _inst_6: decidable_eq ↝
 -/
#print primrec.list_index_of₁ /- _inst_6: decidable_eq ↝
 -/
#print primrec.list_index_of /- _inst_5: decidable_eq ↝
 -/

-- computability\turing_machine.lean
#print turing.TM0.machine /- _inst_2: inhabited ↝
 -/
#print turing.TM1to0.Λ' /- _inst_2: inhabited ↝
_inst_3: inhabited ↝
 -/
#print turing.TM2.stmt.inhabited /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.cfg.inhabited /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.step_aux /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.step /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.reaches /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.supports_stmt /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.stmts₁ /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.stmts₁_self /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.stmts₁_trans /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.stmts₁_supports_stmt_mono /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.stmts /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.stmts_trans /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.supports /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.stmts_supports_stmt /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.step_supports /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.init /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2.eval /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.Γ' /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.Γ'.inhabited /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.Γ'.fintype /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.add_bottom /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.add_bottom_map /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.add_bottom_modify_nth /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.add_bottom_nth_snd /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.add_bottom_nth_succ_fst /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.add_bottom_head_fst /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.st_act.inhabited /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.st_run /- _inst_1: decidable_eq ↝
_inst_2: inhabited ↝
 -/
#print turing.TM2to1.st_var /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.st_write /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.stmt_st_rec /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.supports_run /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.Λ'.inhabited /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_st_act /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_init /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.step_run /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_normal /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_normal_run /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_stmts₁ /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_stmts₁_run /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_respects_aux₂ /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_respects_aux₁ /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_respects_aux₃ /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_respects_aux /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_respects /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_cfg_init /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_eval_dom /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_eval /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_supp /- _inst_1: decidable_eq ↝
 -/
#print turing.TM2to1.tr_supports /- _inst_1: decidable_eq ↝
 -/

-- control\basic.lean
#print fish /- _inst_3: monad ↝ has_bind
 -/
#print succeeds /- _inst_1: alternative ↝ has_orelse has_pure functor
 -/
#print mtry /- _inst_1: alternative ↝ has_orelse has_pure functor
 -/

-- control\bitraversable\instances.lean
#print const.bitraverse /- _inst_2: applicative ↝
 -/

-- control\fold.lean
#print traversable.mfoldl.unop_of_free_monoid /- _inst_2: is_lawful_monad ↝
 -/

-- control\functor.lean
#print functor.comp.has_pure /- _inst_1: applicative ↝ has_pure
_inst_2: applicative ↝ has_pure
 -/

-- control\monad\cont.lean
#print cont_t.monad_lift /- _inst_1: monad ↝ has_bind
 -/
#print writer_t.monad_cont /- _inst_1: monad ↝
 -/
#print state_t.mk_label /- _inst_1: monad ↝
 -/

-- control\monad\writer.lean
#print writer_t.ext /- _inst_1: monad ↝
 -/
#print writer_t.tell /- _inst_1: monad ↝ has_pure
 -/
#print writer_t.pure /- _inst_1: monad ↝ has_pure
 -/
#print writer_t.bind /- _inst_1: monad ↝ has_pure has_bind
 -/
#print writer_t.lift /- _inst_1: monad ↝ functor
 -/
#print writer_t.monad_map /- _inst_2: monad ↝
_inst_3: monad ↝
 -/
#print writer_t.adapt /- _inst_1: monad ↝ functor
 -/
#print writer_t.monad_except /- _inst_1: monad ↝
 -/
#print reader_t.monad_writer /- _inst_1: monad ↝ has_monad_lift
 -/

-- control\traversable\instances.lean
#print option.comp_traverse /- _inst_3: is_lawful_applicative ↝
 -/
#print list.comp_traverse /- _inst_3: is_lawful_applicative ↝
 -/
#print sum.comp_traverse /- _inst_3: is_lawful_applicative ↝
 -/

-- control\uliftable.lean
#print uliftable.adapt_up /- _inst_2: monad ↝ has_bind
 -/
#print uliftable.adapt_down /- _inst_1: monad ↝ has_bind
 -/

-- data\analysis\filter.lean
#print filter.realizer.cofinite /- _inst_1: decidable_eq ↝
 -/

-- data\buffer\basic.lean
#print buffer.decidable_eq /- _inst_1: decidable_eq ↝
 -/

-- data\complex\exponential.lean
#print is_cau_geo_series /- _inst_5: field ↝ domain
 -/

-- data\dfinsupp.lean
#print dfinsupp.mk /- dec: decidable_eq ↝
 -/
#print dfinsupp.mk_apply /- dec: decidable_eq ↝
 -/
#print dfinsupp.mk_injective /- dec: decidable_eq ↝
 -/
#print dfinsupp.single /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_apply /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_zero /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_eq_same /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_eq_of_ne /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_injective /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_eq_single_iff /- dec: decidable_eq ↝
 -/
#print dfinsupp.erase /- dec: decidable_eq ↝
 -/
#print dfinsupp.erase_apply /- dec: decidable_eq ↝
 -/
#print dfinsupp.erase_same /- dec: decidable_eq ↝
 -/
#print dfinsupp.erase_ne /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_add /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_add_hom /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_add_hom_apply /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_add_erase /- dec: decidable_eq ↝
 -/
#print dfinsupp.erase_add_single /- dec: decidable_eq ↝
 -/
#print dfinsupp.induction /- dec: decidable_eq ↝
 -/
#print dfinsupp.induction₂ /- dec: decidable_eq ↝
 -/
#print dfinsupp.add_closure_Union_range_single /- dec: decidable_eq ↝
 -/
#print dfinsupp.add_hom_ext /- dec: decidable_eq ↝
 -/
#print dfinsupp.add_hom_ext' /- dec: decidable_eq ↝
 -/
#print dfinsupp.mk_add /- dec: decidable_eq ↝
 -/
#print dfinsupp.mk_zero /- dec: decidable_eq ↝
 -/
#print dfinsupp.mk_neg /- dec: decidable_eq ↝
 -/
#print dfinsupp.mk_sub /- dec: decidable_eq ↝
 -/
#print dfinsupp.mk.is_add_group_hom /- dec: decidable_eq ↝
 -/
#print dfinsupp.mk_smul /- dec: decidable_eq ↝
 -/
#print dfinsupp.single_smul /- dec: decidable_eq ↝
 -/
#print dfinsupp.support /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_mk_subset /- dec: decidable_eq ↝
 -/
#print dfinsupp.mem_support_to_fun /- dec: decidable_eq ↝
 -/
#print dfinsupp.eq_mk_support /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_zero /- dec: decidable_eq ↝
 -/
#print dfinsupp.mem_support_iff /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_eq_empty /- dec: decidable_eq ↝
 -/
#print dfinsupp.decidable_zero /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_subset_iff /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_single_ne_zero /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_single_subset /- dec: decidable_eq ↝
 -/
#print dfinsupp.map_range_def /- dec: decidable_eq ↝
 -/
#print dfinsupp.map_range_single /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_map_range /- dec: decidable_eq ↝
 -/
#print dfinsupp.zip_with_def /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_zip_with /- dec: decidable_eq ↝
 -/
#print dfinsupp.erase_def /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_erase /- dec: decidable_eq ↝
 -/
#print dfinsupp.filter_def /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_filter /- dec: decidable_eq ↝
 -/
#print dfinsupp.subtype_domain_def /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_subtype_domain /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_add /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_neg /- dec: decidable_eq ↝
 -/
#print dfinsupp.support_smul /- dec: decidable_eq ↝
 -/
#print dfinsupp.decidable_eq /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_map_range_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_map_range_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_zero_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_zero_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_single_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_single_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_neg_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_neg_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_apply /- _inst_1: decidable_eq ↝
 -/
#print dfinsupp.support_sum /- dec: decidable_eq ↝
_inst_1: decidable_eq ↝
 -/
#print dfinsupp.sum_zero /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_one /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_mul /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_add /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_inv /- dec: decidable_eq ↝
_inst_3: comm_group ↝ has_inv is_group_hom comm_monoid
 -/
#print dfinsupp.sum_neg /- dec: decidable_eq ↝
_inst_3: add_comm_group ↝ add_comm_monoid has_neg is_add_group_hom
 -/
#print dfinsupp.prod_add_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_add_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_add_hom /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_add_hom_single /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_add_hom_comp_single /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_add_hom_apply /- dec: decidable_eq ↝
 -/
#print dfinsupp.lift_add_hom /- dec: decidable_eq ↝
 -/
#print dfinsupp.lift_add_hom_symm_apply /- dec: decidable_eq ↝
 -/
#print dfinsupp.lift_add_hom_apply /- dec: decidable_eq ↝
 -/
#print dfinsupp.lift_add_hom_single_add_hom /- dec: decidable_eq ↝
 -/
#print dfinsupp.lift_add_hom_apply_single /- dec: decidable_eq ↝
 -/
#print dfinsupp.lift_add_hom_comp_single /- dec: decidable_eq ↝
 -/
#print dfinsupp.comp_lift_add_hom /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_sub_index /- dec: decidable_eq ↝
_inst_3: add_comm_group ↝ add_comm_monoid add_group
 -/
#print dfinsupp.sum_finset_sum_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_finset_sum_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_sum_index /- dec: decidable_eq ↝
_inst_1: decidable_eq ↝
 -/
#print dfinsupp.sum_sum_index /- dec: decidable_eq ↝
_inst_1: decidable_eq ↝
 -/
#print dfinsupp.sum_single /- dec: decidable_eq ↝
 -/
#print dfinsupp.prod_subtype_domain_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.sum_subtype_domain_index /- dec: decidable_eq ↝
 -/
#print dfinsupp.subtype_domain_finsupp_sum /- _inst_1: decidable_eq ↝
 -/

-- data\equiv\basic.lean
#print equiv.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.prod_extend_right /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.prod_extend_right_apply_eq /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.prod_extend_right_apply_ne /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.eq_of_prod_extend_right_ne /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.fst_prod_extend_right /- _inst_1: decidable_eq ↝
 -/
#print equiv.subtype_equiv_codomain /- _inst_1: decidable_eq ↝
 -/
#print equiv.coe_subtype_equiv_codomain /- _inst_1: decidable_eq ↝
 -/
#print equiv.subtype_equiv_codomain_apply /- _inst_1: decidable_eq ↝
 -/
#print equiv.coe_subtype_equiv_codomain_symm /- _inst_1: decidable_eq ↝
 -/
#print equiv.subtype_equiv_codomain_symm_apply /- _inst_1: decidable_eq ↝
 -/
#print equiv.subtype_equiv_codomain_symm_apply_eq /- _inst_1: decidable_eq ↝
 -/
#print equiv.subtype_equiv_codomain_symm_apply_ne /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_core /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_core_self /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_core_swap_core /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_core_comm /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_self /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_comm /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_apply_def /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_apply_left /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_apply_right /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_apply_of_ne_of_ne /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_comp_apply /- _inst_1: decidable_eq ↝
 -/
#print equiv.swap_inv /- _inst_2: decidable_eq ↝
 -/
#print equiv.symm_trans_swap_trans /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print equiv.swap_mul_self /- _inst_2: decidable_eq ↝
 -/
#print equiv.swap_apply_self /- _inst_2: decidable_eq ↝
 -/
#print equiv.set_value /- _inst_1: decidable_eq ↝
 -/
#print equiv.set_value_eq /- _inst_1: decidable_eq ↝
 -/
#print ulift.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print plift.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print dite_comp_equiv_update /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/

-- data\equiv\encodable\basic.lean
#print directed.le_sequence /- _inst_3: preorder ↝ has_le
 -/
#print quotient.rep /- _inst_1: decidable_rel ↝
 -/
#print quotient.rep_spec /- _inst_1: decidable_rel ↝
 -/
#print encodable_quotient /- _inst_1: decidable_rel ↝
 -/

-- data\equiv\list.lean
#print encodable.encodable_of_list /- _inst_1: decidable_eq ↝
 -/
#print encodable.trunc_encodable_of_fintype /- _inst_1: decidable_eq ↝
 -/
#print encodable.fintype_arrow /- _inst_1: decidable_eq ↝
 -/
#print encodable.fintype_pi /- _inst_1: decidable_eq ↝
 -/

-- data\equiv\ring.lean
#print ring_equiv.trans_apply /- _inst_7: semiring ↝ has_add has_mul
_inst_8: semiring ↝ has_add has_mul
_inst_9: semiring ↝ has_add has_mul
 -/
#print ring_equiv.map_mul /- _inst_1: semiring ↝ has_add has_mul
_inst_2: semiring ↝ has_add has_mul
 -/
#print ring_equiv.map_one /- _inst_1: semiring ↝ monoid has_add
_inst_2: semiring ↝ monoid has_add
 -/
#print ring_equiv.map_add /- _inst_1: semiring ↝ has_add has_mul
_inst_2: semiring ↝ has_add has_mul
 -/
#print ring_equiv.map_zero /- _inst_1: semiring ↝ add_monoid has_mul
_inst_2: semiring ↝ add_monoid has_mul
 -/
#print ring_equiv.map_eq_one_iff /- _inst_1: semiring ↝ monoid has_add
_inst_2: semiring ↝ monoid has_add
 -/
#print ring_equiv.map_eq_zero_iff /- _inst_1: semiring ↝ add_monoid has_mul
_inst_2: semiring ↝ add_monoid has_mul
 -/
#print ring_equiv.map_ne_one_iff /- _inst_1: semiring ↝ monoid has_add
_inst_2: semiring ↝ monoid has_add
 -/
#print ring_equiv.map_ne_zero_iff /- _inst_1: semiring ↝ add_monoid has_mul
_inst_2: semiring ↝ add_monoid has_mul
 -/
#print ring_equiv.map_neg /- _inst_1: ring ↝ add_group has_mul
_inst_2: ring ↝ add_group has_mul
 -/
#print ring_equiv.map_sub /- _inst_1: ring ↝ add_group has_mul
_inst_2: ring ↝ add_group has_mul
 -/

-- data\equiv\transfer_instance.lean
#print equiv.mul_action /- _inst_2: mul_action ↝
 -/
#print equiv.linear_equiv /- _inst_3: semimodule ↝
 -/

-- data\fin_enum.lean
#print fin_enum.of_nodup_list /- _inst_1: decidable_eq ↝
 -/
#print fin_enum.of_list /- _inst_1: decidable_eq ↝
 -/
#print fin_enum.of_surjective /- _inst_1: decidable_eq ↝
 -/
#print fin_enum.of_injective /- _inst_1: decidable_eq ↝
 -/
#print fin_enum.quotient.enum /- _inst_2: decidable_rel ↝
 -/
#print fin_enum.finset.enum /- _inst_1: decidable_eq ↝
 -/
#print fin_enum.finset.mem_enum /- _inst_1: decidable_eq ↝
 -/
#print fin_enum.pi.cons /- _inst_1: decidable_eq ↝
 -/
#print fin_enum.pi /- _inst_1: decidable_eq ↝
 -/
#print fin_enum.mem_pi /- _inst_1: fin_enum ↝
 -/

-- data\finmap.lean
#print list.to_finmap /- _inst_1: decidable_eq ↝
 -/
#print finmap.to_finmap_nil /- _inst_1: decidable_eq ↝
 -/
#print finmap.has_decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_to_finmap /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_list_to_finmap /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_empty /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_is_some /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_eq_none /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_singleton_eq /- _inst_1: decidable_eq ↝
 -/
#print finmap.has_mem.mem.decidable /- _inst_1: decidable_eq ↝
 -/
#print finmap.mem_iff /- _inst_1: decidable_eq ↝
 -/
#print finmap.mem_of_lookup_eq_some /- _inst_1: decidable_eq ↝
 -/
#print finmap.ext_lookup /- _inst_1: decidable_eq ↝
 -/
#print finmap.replace /- _inst_1: decidable_eq ↝
 -/
#print finmap.replace_to_finmap /- _inst_1: decidable_eq ↝
 -/
#print finmap.keys_replace /- _inst_1: decidable_eq ↝
 -/
#print finmap.mem_replace /- _inst_1: decidable_eq ↝
 -/
#print finmap.erase /- _inst_1: decidable_eq ↝
 -/
#print finmap.erase_to_finmap /- _inst_1: decidable_eq ↝
 -/
#print finmap.keys_erase_to_finset /- _inst_1: decidable_eq ↝
 -/
#print finmap.keys_erase /- _inst_1: decidable_eq ↝
 -/
#print finmap.mem_erase /- _inst_1: decidable_eq ↝
 -/
#print finmap.not_mem_erase_self /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_erase /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_erase_ne /- _inst_1: decidable_eq ↝
 -/
#print finmap.erase_erase /- _inst_1: decidable_eq ↝
 -/
#print finmap.sdiff /- _inst_1: decidable_eq ↝
 -/
#print finmap.has_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finmap.insert /- _inst_1: decidable_eq ↝
 -/
#print finmap.insert_to_finmap /- _inst_1: decidable_eq ↝
 -/
#print finmap.insert_entries_of_neg /- _inst_1: decidable_eq ↝
 -/
#print finmap.mem_insert /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_insert /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_insert_of_ne /- _inst_1: decidable_eq ↝
 -/
#print finmap.insert_insert /- _inst_1: decidable_eq ↝
 -/
#print finmap.insert_insert_of_ne /- _inst_1: decidable_eq ↝
 -/
#print finmap.to_finmap_cons /- _inst_1: decidable_eq ↝
 -/
#print finmap.mem_list_to_finmap /- _inst_1: decidable_eq ↝
 -/
#print finmap.insert_singleton_eq /- _inst_1: decidable_eq ↝
 -/
#print finmap.extract /- _inst_1: decidable_eq ↝
 -/
#print finmap.extract_eq_lookup_erase /- _inst_1: decidable_eq ↝
 -/
#print finmap.union /- _inst_1: decidable_eq ↝
 -/
#print finmap.has_union /- _inst_1: decidable_eq ↝
 -/
#print finmap.mem_union /- _inst_1: decidable_eq ↝
 -/
#print finmap.union_to_finmap /- _inst_1: decidable_eq ↝
 -/
#print finmap.keys_union /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_union_left /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_union_right /- _inst_1: decidable_eq ↝
 -/
#print finmap.lookup_union_left_of_not_in /- _inst_1: decidable_eq ↝
 -/
#print finmap.mem_lookup_union /- _inst_1: decidable_eq ↝
 -/
#print finmap.mem_lookup_union_middle /- _inst_1: decidable_eq ↝
 -/
#print finmap.insert_union /- _inst_1: decidable_eq ↝
 -/
#print finmap.union_assoc /- _inst_1: decidable_eq ↝
 -/
#print finmap.empty_union /- _inst_1: decidable_eq ↝
 -/
#print finmap.union_empty /- _inst_1: decidable_eq ↝
 -/
#print finmap.erase_union_singleton /- _inst_1: decidable_eq ↝
 -/
#print finmap.disjoint.decidable_rel /- _inst_1: decidable_eq ↝
 -/
#print finmap.disjoint_union_left /- _inst_1: decidable_eq ↝
 -/
#print finmap.disjoint_union_right /- _inst_1: decidable_eq ↝
 -/
#print finmap.union_comm_of_disjoint /- _inst_1: decidable_eq ↝
 -/
#print finmap.union_cancel /- _inst_1: decidable_eq ↝
 -/

-- data\finset\basic.lean
#print finset.erase_dup_eq_self /- _inst_1: decidable_eq ↝
 -/
#print finset.has_decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print finset.decidable_mem /- h: decidable_eq ↝
 -/
#print finset.decidable_mem' /- _inst_1: decidable_eq ↝
 -/
#print finset.has_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_def /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_val /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_val' /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_val_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_insert_self /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_insert_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_of_mem_insert_of_ne /- _inst_1: decidable_eq ↝
 -/
#print finset.cons_eq_insert /- _inst_2: decidable_eq ↝
 -/
#print finset.coe_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.is_lawful_singleton /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_eq_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_singleton_self_eq /- _inst_1: decidable_eq ↝
 -/
#print finset.insert.comm /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_singleton_comm /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_idem /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_nonempty /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_ne_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.ne_insert_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.subset_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_subset_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.ssubset_iff /- _inst_1: decidable_eq ↝
 -/
#print finset.ssubset_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.induction /- _inst_2: decidable_eq ↝
 -/
#print finset.induction_on /- _inst_2: decidable_eq ↝
 -/
#print finset.subtype_insert_equiv_option /- _inst_1: decidable_eq ↝
 -/
#print finset.has_union /- _inst_1: decidable_eq ↝
 -/
#print finset.union_val_nd /- _inst_1: decidable_eq ↝
 -/
#print finset.union_val /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_union /- _inst_1: decidable_eq ↝
 -/
#print finset.disj_union_eq_union /- _inst_2: decidable_eq ↝
 -/
#print finset.mem_union_left /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_union_right /- _inst_1: decidable_eq ↝
 -/
#print finset.forall_mem_union /- _inst_1: decidable_eq ↝
 -/
#print finset.not_mem_union /- _inst_1: decidable_eq ↝
 -/
#print finset.coe_union /- _inst_1: decidable_eq ↝
 -/
#print finset.union_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.subset_union_left /- _inst_1: decidable_eq ↝
 -/
#print finset.subset_union_right /- _inst_1: decidable_eq ↝
 -/
#print finset.union_subset_union /- _inst_1: decidable_eq ↝
 -/
#print finset.union_comm /- _inst_1: decidable_eq ↝
 -/
#print finset.has_union.union.is_commutative /- _inst_1: decidable_eq ↝
 -/
#print finset.union_assoc /- _inst_1: decidable_eq ↝
 -/
#print finset.has_union.union.is_associative /- _inst_1: decidable_eq ↝
 -/
#print finset.union_idempotent /- _inst_1: decidable_eq ↝
 -/
#print finset.has_union.union.is_idempotent /- _inst_1: decidable_eq ↝
 -/
#print finset.union_left_comm /- _inst_1: decidable_eq ↝
 -/
#print finset.union_right_comm /- _inst_1: decidable_eq ↝
 -/
#print finset.union_self /- _inst_1: decidable_eq ↝
 -/
#print finset.union_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.empty_union /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_eq /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_union /- _inst_1: decidable_eq ↝
 -/
#print finset.union_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_union_distrib /- _inst_1: decidable_eq ↝
 -/
#print finset.union_eq_left_iff_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.left_eq_union_iff_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.union_eq_right_iff_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.right_eq_union_iff_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.has_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_val_nd /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_val /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_of_mem_inter_left /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_of_mem_inter_right /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_inter_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_subset_left /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_subset_right /- _inst_1: decidable_eq ↝
 -/
#print finset.subset_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.coe_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.union_inter_cancel_left /- _inst_1: decidable_eq ↝
 -/
#print finset.union_inter_cancel_right /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_comm /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_assoc /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_left_comm /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_right_comm /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_self /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.empty_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_union_self /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_inter_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_insert_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_inter_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_insert_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.singleton_inter_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.singleton_inter_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_singleton_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_singleton_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_subset_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_subset_inter_right /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_subset_inter_left /- _inst_1: decidable_eq ↝
 -/
#print finset.lattice /- _inst_1: decidable_eq ↝
 -/
#print finset.sup_eq_union /- _inst_1: decidable_eq ↝
 -/
#print finset.inf_eq_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.semilattice_inf_bot /- _inst_1: decidable_eq ↝
 -/
#print finset.semilattice_sup_bot /- _inst_2: decidable_eq ↝
 -/
#print finset.distrib_lattice /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_distrib_left /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_distrib_right /- _inst_1: decidable_eq ↝
 -/
#print finset.union_distrib_left /- _inst_1: decidable_eq ↝
 -/
#print finset.union_distrib_right /- _inst_1: decidable_eq ↝
 -/
#print finset.union_eq_empty_iff /- _inst_1: decidable_eq ↝
 -/
#print finset.erase /- _inst_1: decidable_eq ↝
 -/
#print finset.erase_val /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_erase /- _inst_1: decidable_eq ↝
 -/
#print finset.not_mem_erase /- _inst_1: decidable_eq ↝
 -/
#print finset.erase_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.ne_of_mem_erase /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_of_mem_erase /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_erase_of_ne_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.eq_of_mem_of_not_mem_erase /- _inst_1: decidable_eq ↝
 -/
#print finset.erase_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_erase /- _inst_1: decidable_eq ↝
 -/
#print finset.erase_subset_erase /- _inst_1: decidable_eq ↝
 -/
#print finset.erase_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.coe_erase /- _inst_1: decidable_eq ↝
 -/
#print finset.erase_ssubset /- _inst_1: decidable_eq ↝
 -/
#print finset.erase_eq_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.subset_insert_iff /- _inst_1: decidable_eq ↝
 -/
#print finset.erase_insert_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_erase_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.has_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finset.not_mem_sdiff_of_mem_right /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_union_of_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.union_sdiff_of_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_sdiff_self /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_inter_self /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_self /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_inter_distrib_right /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_inter_self_left /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_inter_self_right /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_subset_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_subset_self /- _inst_1: decidable_eq ↝
 -/
#print finset.coe_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finset.union_sdiff_self_eq_union /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_union_self_eq_union /- _inst_1: decidable_eq ↝
 -/
#print finset.union_sdiff_symm /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_union_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_idem /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_eq_empty_iff_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.empty_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_sdiff_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_sdiff_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.insert_sdiff_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_insert_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.union_sdiff_distrib /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_union_distrib /- _inst_1: decidable_eq ↝
 -/
#print finset.union_sdiff_self /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_singleton_eq_erase /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_sdiff_self_left /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_eq_inter_of_sdiff_eq_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finset.piecewise_insert_self /- _inst_1: decidable_eq ↝
 -/
#print finset.piecewise_insert_of_ne /- _inst_2: decidable_eq ↝
 -/
#print finset.piecewise_insert /- _inst_2: decidable_eq ↝
 -/
#print finset.piecewise_singleton /- _inst_2: decidable_eq ↝
 -/
#print finset.update_eq_piecewise /- _inst_2: decidable_eq ↝
 -/
#print finset.update_piecewise /- _inst_2: decidable_eq ↝
 -/
#print finset.update_piecewise_of_mem /- _inst_2: decidable_eq ↝
 -/
#print finset.update_piecewise_of_not_mem /- _inst_2: decidable_eq ↝
 -/
#print finset.filter_union /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_union_right /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_mem_eq_inter /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_inter /- _inst_3: decidable_eq ↝
 -/
#print finset.inter_filter /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_insert /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_or /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_and /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_not /- _inst_3: decidable_eq ↝
 -/
#print finset.sdiff_eq_filter /- _inst_3: decidable_eq ↝
 -/
#print finset.sdiff_eq_self /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_union_filter_neg_eq /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_inter_filter_neg_eq /- _inst_3: decidable_eq ↝
 -/
#print finset.subset_union_elim /- _inst_3: decidable_eq ↝
 -/
#print finset.filter_eq /- _inst_4: decidable_eq ↝
 -/
#print finset.filter_eq' /- _inst_4: decidable_eq ↝
 -/
#print finset.filter_ne /- _inst_4: decidable_eq ↝
 -/
#print finset.filter_ne' /- _inst_4: decidable_eq ↝
 -/
#print finset.exists_mem_insert /- d: decidable_eq ↝
 -/
#print finset.forall_mem_insert /- d: decidable_eq ↝
 -/
#print multiset.to_finset /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_val /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_eq /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_to_finset /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_cons /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_add /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_nsmul /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_union /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_eq_empty /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_subset /- _inst_1: decidable_eq ↝
 -/
#print list.to_finset /- _inst_1: decidable_eq ↝
 -/
#print list.to_finset_val /- _inst_1: decidable_eq ↝
 -/
#print list.to_finset_eq /- _inst_1: decidable_eq ↝
 -/
#print list.mem_to_finset /- _inst_1: decidable_eq ↝
 -/
#print list.to_finset_nil /- _inst_1: decidable_eq ↝
 -/
#print list.to_finset_cons /- _inst_1: decidable_eq ↝
 -/
#print list.to_finset_surjective /- _inst_1: decidable_eq ↝
 -/
#print finset.map_to_finset /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.map_union /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.map_inter /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.map_insert /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.image /- _inst_1: decidable_eq ↝
 -/
#print finset.image_val /- _inst_1: decidable_eq ↝
 -/
#print finset.image_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_image /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_image_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.filter_mem_image_eq_image /- _inst_1: decidable_eq ↝
 -/
#print finset.fiber_nonempty_iff_mem_image /- _inst_1: decidable_eq ↝
 -/
#print finset.coe_image /- _inst_1: decidable_eq ↝
 -/
#print finset.nonempty.image /- _inst_1: decidable_eq ↝
 -/
#print finset.image_to_finset /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.image_val_of_inj_on /- _inst_1: decidable_eq ↝
 -/
#print finset.image_id /- _inst_2: decidable_eq ↝
 -/
#print finset.image_image /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.image_subset_image /- _inst_1: decidable_eq ↝
 -/
#print finset.image_subset_iff /- _inst_1: decidable_eq ↝
 -/
#print finset.image_mono /- _inst_1: decidable_eq ↝
 -/
#print finset.coe_image_subset_range /- _inst_1: decidable_eq ↝
 -/
#print finset.image_filter /- _inst_1: decidable_eq ↝
 -/
#print finset.image_union /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.image_inter /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.image_singleton /- _inst_1: decidable_eq ↝
 -/
#print finset.image_insert /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.image_eq_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.attach_image_val /- _inst_2: decidable_eq ↝
 -/
#print finset.attach_insert /- _inst_2: decidable_eq ↝
 -/
#print finset.map_eq_image /- _inst_1: decidable_eq ↝
 -/
#print finset.image_const /- _inst_1: decidable_eq ↝
 -/
#print finset.subset_image_iff /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_map /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.card_insert_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.card_insert_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.card_insert_le /- _inst_1: decidable_eq ↝
 -/
#print finset.card_singleton_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.card_erase_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.card_erase_lt_of_mem /- _inst_1: decidable_eq ↝
 -/
#print finset.card_erase_le /- _inst_1: decidable_eq ↝
 -/
#print finset.pred_card_le_card_erase /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_card_le /- _inst_1: decidable_eq ↝
 -/
#print list.to_finset_card_le /- _inst_1: decidable_eq ↝
 -/
#print finset.card_image_le /- _inst_1: decidable_eq ↝
 -/
#print finset.card_image_of_inj_on /- _inst_1: decidable_eq ↝
 -/
#print finset.card_image_of_injective /- _inst_1: decidable_eq ↝
 -/
#print finset.fiber_card_ne_zero_iff_mem_image /- _inst_1: decidable_eq ↝
 -/
#print finset.card_eq_succ /- _inst_1: decidable_eq ↝
 -/
#print finset.case_strong_induction_on /- _inst_1: decidable_eq ↝
 -/
#print finset.card_union_add_card_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.card_union_le /- _inst_1: decidable_eq ↝
 -/
#print finset.card_union_eq /- _inst_1: decidable_eq ↝
 -/
#print finset.bind /- _inst_1: decidable_eq ↝
 -/
#print finset.bind_val /- _inst_1: decidable_eq ↝
 -/
#print finset.bind_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_bind /- _inst_1: decidable_eq ↝
 -/
#print finset.bind_insert /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.singleton_bind /- _inst_1: decidable_eq ↝
 -/
#print finset.bind_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.inter_bind /- _inst_1: decidable_eq ↝
 -/
#print finset.image_bind /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.bind_image /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.bind_to_finset /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.bind_mono /- _inst_1: decidable_eq ↝
 -/
#print finset.bind_subset_bind_of_subset_left /- _inst_1: decidable_eq ↝
 -/
#print finset.bind_singleton /- _inst_1: decidable_eq ↝
 -/
#print finset.bind_singleton_eq_self /- _inst_2: decidable_eq ↝
 -/
#print finset.bind_filter_eq_of_maps_to /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.image_bind_filter_eq /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.subset_product /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.product_eq_bind /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print finset.sigma_eq_bind /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_left /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_val /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_iff_inter_eq_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.decidable_disjoint /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_right /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_iff_ne /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_of_subset_left /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_of_subset_right /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_empty_left /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_empty_right /- _inst_1: decidable_eq ↝
 -/
#print finset.singleton_disjoint /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_singleton /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_insert_left /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_insert_right /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_union_left /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_union_right /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_disjoint /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_sdiff_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_eq_self_iff_disjoint /- _inst_1: decidable_eq ↝
 -/
#print finset.sdiff_eq_self_of_disjoint /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_self_iff_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_bind_left /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_bind_right /- _inst_1: decidable_eq ↝
 -/
#print finset.card_disjoint_union /- _inst_1: decidable_eq ↝
 -/
#print finset.card_sdiff /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_filter /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_filter_filter /- _inst_1: decidable_eq ↝
 -/
#print finset.disjoint_iff_disjoint_coe /- _inst_2: decidable_eq ↝
 -/
#print finset.diag /- _inst_1: decidable_eq ↝
 -/
#print finset.off_diag /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_diag /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_off_diag /- _inst_1: decidable_eq ↝
 -/
#print finset.diag_card /- _inst_1: decidable_eq ↝
 -/
#print finset.off_diag_card /- _inst_1: decidable_eq ↝
 -/
#print list.to_finset_card_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print multiset.to_finset_card_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print multiset.disjoint_to_finset /- _inst_1: decidable_eq ↝
 -/

-- data\finset\fold.lean
#print finset.fold_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.fold_image /- _inst_1: decidable_eq ↝
 -/
#print finset.fold_union_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.fold_insert_idem /- _inst_1: decidable_eq ↝
 -/
#print finset.fold_union_empty_singleton /- _inst_1: decidable_eq ↝
 -/
#print finset.fold_sup_bot_singleton /- _inst_1: decidable_eq ↝
 -/

-- data\finset\gcd.lean
#print finset.lcm_insert /- _inst_4: decidable_eq ↝
 -/
#print finset.lcm_union /- _inst_4: decidable_eq ↝
 -/
#print finset.gcd_insert /- _inst_4: decidable_eq ↝
 -/
#print finset.gcd_union /- _inst_4: decidable_eq ↝
 -/
#print finset.gcd_eq_of_dvd_sub /- _inst_1: nontrivial ↝ nonempty
 -/

-- data\finset\lattice.lean
#print finset.sup_insert /- _inst_2: decidable_eq ↝
 -/
#print finset.sup_union /- _inst_2: decidable_eq ↝
 -/
#print finset.sup_lt_iff /- _inst_2: is_total ↝
 -/
#print finset.comp_sup_eq_sup_comp_of_is_total /- _inst_2: is_total ↝
 -/
#print finset.mem_sup /- _inst_2: decidable_eq ↝
 -/
#print finset.inf_insert /- _inst_2: decidable_eq ↝
 -/
#print finset.inf_union /- _inst_2: decidable_eq ↝
 -/
#print finset.lt_inf_iff /- h: is_total ↝
 -/
#print finset.comp_inf_eq_inf_comp_of_is_total /- h: is_total ↝
 -/
#print multiset.count_sup /- _inst_1: decidable_eq ↝
 -/
#print finset.supr_option_to_finset /- _inst_1: complete_lattice ↝ has_Sup
 -/
#print finset.supr_union /- _inst_2: decidable_eq ↝
 -/
#print finset.infi_union /- _inst_2: decidable_eq ↝
 -/
#print finset.supr_insert /- _inst_2: decidable_eq ↝
 -/
#print finset.infi_insert /- _inst_2: decidable_eq ↝
 -/
#print finset.supr_finset_image /- _inst_2: decidable_eq ↝
 -/
#print finset.infi_finset_image /- _inst_2: decidable_eq ↝
 -/
#print finset.supr_insert_update /- _inst_2: decidable_eq ↝
 -/
#print finset.infi_insert_update /- _inst_2: decidable_eq ↝
 -/
#print finset.supr_bind /- _inst_2: decidable_eq ↝
 -/
#print finset.infi_bind /- _inst_2: decidable_eq ↝
 -/
#print finset.bUnion_union /- _inst_1: decidable_eq ↝
 -/
#print finset.bInter_inter /- _inst_1: decidable_eq ↝
 -/
#print finset.bUnion_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.bInter_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.bUnion_finset_image /- _inst_1: decidable_eq ↝
 -/
#print finset.bInter_finset_image /- _inst_1: decidable_eq ↝
 -/
#print finset.bUnion_insert_update /- _inst_1: decidable_eq ↝
 -/
#print finset.bInter_insert_update /- _inst_1: decidable_eq ↝
 -/
#print finset.bUnion_bind /- _inst_1: decidable_eq ↝
 -/
#print finset.bInter_bind /- _inst_1: decidable_eq ↝
 -/

-- data\finset\pi.lean
#print finset.pi /- _inst_1: decidable_eq ↝
 -/
#print finset.pi_val /- _inst_1: decidable_eq ↝
 -/
#print finset.mem_pi /- _inst_1: decidable_eq ↝
 -/
#print finset.pi.cons /- _inst_1: decidable_eq ↝
 -/
#print finset.pi.cons_same /- _inst_1: decidable_eq ↝
 -/
#print finset.pi.cons_ne /- _inst_1: decidable_eq ↝
 -/
#print finset.pi_cons_injective /- _inst_1: decidable_eq ↝
 -/
#print finset.pi_empty /- _inst_1: decidable_eq ↝
 -/
#print finset.pi_insert /- _inst_1: decidable_eq ↝
 -/
#print finset.pi_singletons /- _inst_1: decidable_eq ↝
 -/
#print finset.pi_const_singleton /- _inst_1: decidable_eq ↝
 -/
#print finset.pi_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.pi_disjoint_of_disjoint /- _inst_1: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/

-- data\finset\powerset.lean
#print finset.powerset_insert /- _inst_1: decidable_eq ↝
 -/

-- data\finset\preimage.lean
#print finset.image_subset_iff_subset_preimage /- _inst_1: decidable_eq ↝
 -/
#print finset.image_preimage /- _inst_1: decidable_eq ↝
 -/
#print finset.image_preimage_of_bij /- _inst_1: decidable_eq ↝
 -/
#print finset.sigma_preimage_mk /- _inst_1: decidable_eq ↝
 -/
#print finset.sigma_preimage_mk_of_subset /- _inst_1: decidable_eq ↝
 -/
#print finset.sigma_image_fst_preimage_mk /- _inst_1: decidable_eq ↝
 -/

-- data\finset\sort.lean
#print finset.sort /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print finset.sort_sorted /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print finset.sort_eq /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print finset.sort_nodup /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print finset.sort_to_finset /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
_inst_5: decidable_eq ↝
 -/
#print finset.mem_sort /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print finset.length_sort /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/

-- data\finsupp\basic.lean
#print finsupp.finsupp.decidable_eq /- _inst_2: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print finsupp.prod_add_index /- _inst_1: add_comm_monoid ↝ add_monoid
 -/
#print finsupp.sum_add_index /- _inst_1: add_comm_monoid ↝ add_monoid
 -/
#print finsupp.sum_sub_index /- _inst_1: add_comm_group ↝ add_comm_monoid add_group
_inst_2: add_comm_group ↝ add_comm_monoid add_group
 -/
#print finsupp.prod_sum_index /- _inst_1: add_comm_monoid ↝ has_zero
 -/
#print finsupp.sum_sum_index /- _inst_1: add_comm_monoid ↝ has_zero
 -/
#print finsupp.eq_zero_of_comap_domain_eq_zero /- _inst_1: add_comm_monoid ↝ has_zero
 -/
#print finsupp.comap_has_scalar /- _inst_2: mul_action ↝
 -/
#print finsupp.comap_mul_action /- _inst_2: mul_action ↝
 -/
#print finsupp.comap_distrib_mul_action /- _inst_2: mul_action ↝
 -/
#print finsupp.comap_smul_single /- _inst_2: mul_action ↝
 -/
#print finsupp.comap_smul_apply /- _inst_2: mul_action ↝
 -/
#print finsupp.has_scalar /- _inst_3: semimodule ↝
 -/
#print finsupp.smul_apply' /- _inst_2: semimodule ↝ has_scalar
 -/
#print finsupp.semimodule /- _inst_3: semimodule ↝
 -/
#print finsupp.support_smul /- _inst_2: semimodule ↝
 -/
#print finsupp.filter_smul /- _inst_2: semimodule ↝
 -/
#print finsupp.map_domain_smul /- _inst_2: semimodule ↝
 -/
#print finsupp.smul_single /- _inst_2: semimodule ↝
 -/
#print finsupp.smul_apply /- _inst_1: semiring ↝ has_zero
 -/
#print finsupp.sum_smul_index' /- _inst_3: semimodule ↝
 -/
#print finsupp.sum_mul /- _inst_1: semiring ↝ has_zero
 -/
#print finsupp.mul_sum /- _inst_1: semiring ↝ has_zero
 -/

-- data\finsupp\lattice.lean
#print finsupp.le_def /- _inst_4: partial_order ↝ preorder
 -/
#print finsupp.support_inf /- _inst_3: canonically_linear_ordered_add_monoid ↝ canonically_ordered_add_monoid linear_order
 -/
#print finsupp.support_sup /- _inst_3: canonically_linear_ordered_add_monoid ↝ canonically_ordered_add_monoid semilattice_sup_bot
 -/
#print finsupp.bot_eq_zero /- _inst_3: canonically_linear_ordered_add_monoid ↝ canonically_ordered_add_monoid
 -/

-- data\fintype\basic.lean
#print finset.boolean_algebra /- _inst_2: decidable_eq ↝
 -/
#print finset.compl_eq_univ_sdiff /- _inst_2: decidable_eq ↝
 -/
#print finset.mem_compl /- _inst_2: decidable_eq ↝
 -/
#print finset.coe_compl /- _inst_2: decidable_eq ↝
 -/
#print finset.univ_inter /- _inst_2: decidable_eq ↝
 -/
#print finset.inter_univ /- _inst_2: decidable_eq ↝
 -/
#print fintype.decidable_eq_equiv_fintype /- _inst_1: decidable_eq ↝
 -/
#print fintype.decidable_injective_fintype /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print fintype.decidable_surjective_fintype /- _inst_1: decidable_eq ↝
 -/
#print fintype.decidable_bijective_fintype /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print fintype.decidable_left_inverse_fintype /- _inst_1: decidable_eq ↝
 -/
#print fintype.decidable_right_inverse_fintype /- _inst_1: decidable_eq ↝
 -/
#print fintype.of_multiset /- _inst_1: decidable_eq ↝
 -/
#print fintype.of_list /- _inst_1: decidable_eq ↝
 -/
#print fintype.equiv_fin_of_forall_mem_list /- _inst_1: decidable_eq ↝
 -/
#print fintype.equiv_fin /- _inst_1: decidable_eq ↝
 -/
#print fintype.of_surjective /- _inst_1: decidable_eq ↝
 -/
#print finset.card_univ_diff /- _inst_1: decidable_eq ↝
 -/
#print finset.card_compl /- _inst_1: decidable_eq ↝
 -/
#print unique.fintype /- _inst_1: unique ↝ inhabited subsingleton
 -/
#print univ_unique /- _inst_1: unique ↝ inhabited fintype
 -/
#print fintype.fintype_prod_left /- _inst_1: decidable_eq ↝
 -/
#print fintype.fintype_prod_right /- _inst_1: decidable_eq ↝
 -/
#print fintype.coe_image_univ /- _inst_2: decidable_eq ↝
 -/
#print list.subtype.fintype /- _inst_1: decidable_eq ↝
 -/
#print multiset.subtype.fintype /- _inst_1: decidable_eq ↝
 -/
#print fintype.pi_finset /- _inst_1: decidable_eq ↝
 -/
#print fintype.mem_pi_finset /- _inst_1: decidable_eq ↝
 -/
#print fintype.pi_finset_subset /- _inst_1: decidable_eq ↝
 -/
#print fintype.pi_finset_disjoint_of_disjoint /- _inst_1: decidable_eq ↝
 -/
#print pi.fintype /- _inst_1: decidable_eq ↝
 -/
#print fintype.pi_finset_univ /- _inst_1: decidable_eq ↝
 -/
#print quotient.fintype /- _inst_2: decidable_rel ↝
 -/
#print finset.univ_pi_univ /- _inst_1: decidable_eq ↝
 -/
#print mem_image_univ_iff_mem_range /- _inst_2: decidable_eq ↝
 -/
#print quotient.fin_choice_aux /- _inst_1: decidable_eq ↝
 -/
#print quotient.fin_choice_aux_eq /- _inst_1: decidable_eq ↝
 -/
#print quotient.fin_choice /- _inst_1: decidable_eq ↝
 -/
#print quotient.fin_choice_eq /- _inst_1: decidable_eq ↝
 -/
#print perms_of_list /- _inst_1: decidable_eq ↝
 -/
#print length_perms_of_list /- _inst_1: decidable_eq ↝
 -/
#print mem_perms_of_list_of_mem /- _inst_1: decidable_eq ↝
 -/
#print mem_of_mem_perms_of_list /- _inst_1: decidable_eq ↝
 -/
#print mem_perms_of_list_iff /- _inst_1: decidable_eq ↝
 -/
#print nodup_perms_of_list /- _inst_1: decidable_eq ↝
 -/
#print perms_of_finset /- _inst_1: decidable_eq ↝
 -/
#print mem_perms_of_finset_iff /- _inst_1: decidable_eq ↝
 -/
#print card_perms_of_finset /- _inst_1: decidable_eq ↝
 -/
#print fintype_perm /- _inst_1: decidable_eq ↝
 -/
#print equiv.fintype /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print fintype.card_perm /- _inst_1: decidable_eq ↝
 -/
#print fintype.card_equiv /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print fintype.bij_inv /- _inst_2: decidable_eq ↝
 -/
#print fintype.left_inverse_bij_inv /- _inst_2: decidable_eq ↝
 -/
#print fintype.right_inverse_bij_inv /- _inst_2: decidable_eq ↝
 -/
#print fintype.bijective_bij_inv /- _inst_2: decidable_eq ↝
 -/
#print fintype.preorder.well_founded /- _inst_2: preorder ↝ has_lt is_irrefl is_trans
 -/
#print fintype.linear_order.is_well_order /- _inst_2: linear_order ↝ is_trichotomous preorder
 -/
#print infinite.nonempty /- _inst_1: infinite ↝ nonempty
 -/

-- data\fintype\card.lean
#print fintype.sum_extend_by_zero /- _inst_1: decidable_eq ↝
 -/
#print fintype.prod_extend_by_one /- _inst_1: decidable_eq ↝
 -/
#print is_compl.prod_mul_prod /- _inst_2: decidable_eq ↝
 -/
#print is_compl.sum_add_sum /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_mul_prod_compl /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_add_sum_compl /- _inst_2: decidable_eq ↝
 -/
#print finset.sum_compl_add_sum /- _inst_2: decidable_eq ↝
 -/
#print finset.prod_compl_mul_prod /- _inst_2: decidable_eq ↝
 -/
#print finset.card_pi /- _inst_1: decidable_eq ↝
 -/
#print fintype.card_pi_finset /- _inst_1: decidable_eq ↝
 -/
#print fintype.card_pi /- _inst_1: decidable_eq ↝
 -/
#print fintype.card_fun /- _inst_1: decidable_eq ↝
 -/
#print finset.sum_univ_pi /- _inst_1: decidable_eq ↝
 -/
#print finset.prod_univ_pi /- _inst_1: decidable_eq ↝
 -/
#print finset.prod_univ_sum /- _inst_1: decidable_eq ↝
 -/
#print finset.sum_fiberwise /- _inst_1: decidable_eq ↝
 -/
#print finset.prod_fiberwise /- _inst_1: decidable_eq ↝
 -/
#print fintype.prod_fiberwise /- _inst_2: decidable_eq ↝
 -/
#print fintype.sum_fiberwise /- _inst_2: decidable_eq ↝
 -/

-- data\fp\basic.lean
#print fp.div_nat_lt_two_pow /- C: fp.float_cfg ↝
 -/

-- data\hash_map.lean
#print hash_map.find_aux /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find_aux_iff /- _inst_1: decidable_eq ↝
 -/
#print hash_map.contains_aux /- _inst_1: decidable_eq ↝
 -/
#print hash_map.contains_aux_iff /- _inst_1: decidable_eq ↝
 -/
#print hash_map.replace_aux /- _inst_1: decidable_eq ↝
 -/
#print hash_map.erase_aux /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.idx_enum /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.idx_enum_1 /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.as_list_nodup /- _inst_1: decidable_eq ↝
 -/
#print hash_map.mk_valid /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.find_aux_iff /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.contains_aux_iff /- _inst_1: decidable_eq ↝
 -/
#print hash_map.append_of_modify /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.modify /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.replace_aux /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.replace /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.insert /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.erase_aux /- _inst_1: decidable_eq ↝
 -/
#print hash_map.valid.erase /- _inst_1: decidable_eq ↝
 -/
#print mk_hash_map /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find /- _inst_1: decidable_eq ↝
 -/
#print hash_map.contains /- _inst_1: decidable_eq ↝
 -/
#print hash_map.has_mem /- _inst_1: decidable_eq ↝
 -/
#print hash_map.fold /- _inst_1: decidable_eq ↝
 -/
#print hash_map.entries /- _inst_1: decidable_eq ↝
 -/
#print hash_map.keys /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find_iff /- _inst_1: decidable_eq ↝
 -/
#print hash_map.contains_iff /- _inst_1: decidable_eq ↝
 -/
#print hash_map.entries_empty /- _inst_1: decidable_eq ↝
 -/
#print hash_map.keys_empty /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find_empty /- _inst_1: decidable_eq ↝
 -/
#print hash_map.not_contains_empty /- _inst_1: decidable_eq ↝
 -/
#print hash_map.insert_lemma /- _inst_1: decidable_eq ↝
 -/
#print hash_map.insert /- _inst_1: decidable_eq ↝
 -/
#print hash_map.mem_insert /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find_insert_eq /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find_insert_ne /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find_insert /- _inst_1: decidable_eq ↝
 -/
#print hash_map.insert_all /- _inst_1: decidable_eq ↝
 -/
#print hash_map.of_list /- _inst_1: decidable_eq ↝
 -/
#print hash_map.erase /- _inst_1: decidable_eq ↝
 -/
#print hash_map.mem_erase /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find_erase_eq /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find_erase_ne /- _inst_1: decidable_eq ↝
 -/
#print hash_map.find_erase /- _inst_1: decidable_eq ↝
 -/
#print hash_map.has_to_string /- _inst_1: decidable_eq ↝
 -/

-- data\holor.lean
#print holor.zero_mul /- _inst_1: ring ↝ mul_zero_class
 -/
#print holor.mul_zero /- _inst_1: ring ↝ mul_zero_class
 -/
#print holor.mul_scalar_mul /- _inst_1: monoid ↝ has_mul
 -/
#print holor.unit_vec /- _inst_1: monoid ↝ has_one
_inst_2: add_monoid ↝ has_zero
 -/
#print holor.slice_unit_vec_mul /- _inst_1: ring ↝ semiring
 -/
#print holor.cprank_max_nil /- _inst_1: monoid ↝ has_mul
 -/
#print holor.cprank_max_1 /- _inst_1: monoid ↝ has_mul
 -/
#print holor.cprank_max_sum /- _inst_1: ring ↝ monoid add_comm_monoid
 -/

-- data\indicator_function.lean
#print set.indicator_smul /- _inst_3: distrib_mul_action ↝
 -/
#print set.indicator_prod_one /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/

-- data\int\cast.lean
#print int.cast_bit0 /- _inst_1: ring ↝ has_one add_group
 -/
#print int.cast_nonneg /- _inst_1: linear_ordered_ring ↝ ordered_add_comm_group linear_ordered_semiring
 -/
#print int.cast_min /- _inst_1: linear_ordered_comm_ring ↝ linear_ordered_ring
 -/
#print int.cast_max /- _inst_1: linear_ordered_comm_ring ↝ linear_ordered_ring
 -/
#print int.coe_int_dvd /- _inst_1: comm_ring ↝ ring comm_semiring
 -/
#print ring_hom.eq_int_cast /- _inst_1: ring ↝ add_group semiring
 -/

-- data\lazy_list\basic.lean
#print thunk.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print lazy_list.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print lazy_list.mem.decidable /- _inst_1: decidable_eq ↝
 -/

-- data\list\alist.lean
#print list.to_alist /- _inst_1: decidable_eq ↝
 -/
#print alist.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_empty /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_is_some /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_eq_none /- _inst_1: decidable_eq ↝
 -/
#print alist.perm_lookup /- _inst_1: decidable_eq ↝
 -/
#print alist.has_mem.mem.decidable /- _inst_1: decidable_eq ↝
 -/
#print alist.replace /- _inst_1: decidable_eq ↝
 -/
#print alist.keys_replace /- _inst_1: decidable_eq ↝
 -/
#print alist.mem_replace /- _inst_1: decidable_eq ↝
 -/
#print alist.perm_replace /- _inst_1: decidable_eq ↝
 -/
#print alist.erase /- _inst_1: decidable_eq ↝
 -/
#print alist.keys_erase /- _inst_1: decidable_eq ↝
 -/
#print alist.mem_erase /- _inst_1: decidable_eq ↝
 -/
#print alist.perm_erase /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_erase /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_erase_ne /- _inst_1: decidable_eq ↝
 -/
#print alist.erase_erase /- _inst_1: decidable_eq ↝
 -/
#print alist.insert /- _inst_1: decidable_eq ↝
 -/
#print alist.insert_entries /- _inst_1: decidable_eq ↝
 -/
#print alist.insert_entries_of_neg /- _inst_1: decidable_eq ↝
 -/
#print alist.mem_insert /- _inst_1: decidable_eq ↝
 -/
#print alist.keys_insert /- _inst_1: decidable_eq ↝
 -/
#print alist.perm_insert /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_insert /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_insert_ne /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_to_alist /- _inst_1: decidable_eq ↝
 -/
#print alist.insert_insert /- _inst_1: decidable_eq ↝
 -/
#print alist.insert_insert_of_ne /- _inst_1: decidable_eq ↝
 -/
#print alist.insert_singleton_eq /- _inst_1: decidable_eq ↝
 -/
#print alist.entries_to_alist /- _inst_1: decidable_eq ↝
 -/
#print alist.to_alist_cons /- _inst_1: decidable_eq ↝
 -/
#print alist.extract /- _inst_1: decidable_eq ↝
 -/
#print alist.extract_eq_lookup_erase /- _inst_1: decidable_eq ↝
 -/
#print alist.union /- _inst_1: decidable_eq ↝
 -/
#print alist.has_union /- _inst_1: decidable_eq ↝
 -/
#print alist.union_entries /- _inst_1: decidable_eq ↝
 -/
#print alist.empty_union /- _inst_1: decidable_eq ↝
 -/
#print alist.union_empty /- _inst_1: decidable_eq ↝
 -/
#print alist.mem_union /- _inst_1: decidable_eq ↝
 -/
#print alist.perm_union /- _inst_1: decidable_eq ↝
 -/
#print alist.union_erase /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_union_left /- _inst_1: decidable_eq ↝
 -/
#print alist.lookup_union_right /- _inst_1: decidable_eq ↝
 -/
#print alist.mem_lookup_union /- _inst_1: decidable_eq ↝
 -/
#print alist.mem_lookup_union_middle /- _inst_1: decidable_eq ↝
 -/
#print alist.insert_union /- _inst_1: decidable_eq ↝
 -/
#print alist.union_assoc /- _inst_1: decidable_eq ↝
 -/
#print alist.union_comm_of_disjoint /- _inst_1: decidable_eq ↝
 -/

-- data\list\bag_inter.lean
#print list.nil_bag_inter /- _inst_1: decidable_eq ↝
 -/
#print list.bag_inter_nil /- _inst_1: decidable_eq ↝
 -/
#print list.cons_bag_inter_of_pos /- _inst_1: decidable_eq ↝
 -/
#print list.cons_bag_inter_of_neg /- _inst_1: decidable_eq ↝
 -/
#print list.mem_bag_inter /- _inst_1: decidable_eq ↝
 -/
#print list.count_bag_inter /- _inst_1: decidable_eq ↝
 -/
#print list.bag_inter_sublist_left /- _inst_1: decidable_eq ↝
 -/
#print list.bag_inter_nil_iff_inter_nil /- _inst_1: decidable_eq ↝
 -/

-- data\list\basic.lean
#print list.insert_neg /- _inst_1: decidable_eq ↝
 -/
#print list.insert_pos /- _inst_1: decidable_eq ↝
 -/
#print list.doubleton_eq /- _inst_1: decidable_eq ↝
 -/
#print list.decidable_sublist /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_nil /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_cons /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_cons_eq /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_cons_self /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_cons_ne /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_eq_length /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_le_length /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_lt_length /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_nth_le /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_nth /- _inst_1: decidable_eq ↝
 -/
#print list.index_of_inj /- _inst_1: decidable_eq ↝
 -/
#print list.prod_nil /- _inst_1: monoid ↝ has_one has_mul
 -/
#print list.sum_nil /- _inst_1: add_monoid ↝ has_zero has_add
 -/
#print list.prod_ne_zero /- _inst_2: domain ↝ monoid_with_zero nontrivial no_zero_divisors
 -/
#print list.eq_of_sum_take_eq /- _inst_1: add_left_cancel_monoid ↝ add_monoid add_left_cancel_semigroup
 -/
#print list.length_pos_of_sum_pos /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_monoid preorder
 -/
#print list.prod_erase /- _inst_1: decidable_eq ↝
 -/
#print list.sum_erase /- _inst_1: decidable_eq ↝
 -/
#print list.dvd_prod /- _inst_1: comm_monoid ↝ monoid comm_semigroup
 -/
#print list.exists_lt_of_sum_lt /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid linear_order
 -/
#print list.alternating_prod_nil /- _inst_1: comm_group ↝ has_inv has_one has_mul
 -/
#print list.alternating_sum_nil /- _inst_1: add_comm_group ↝ has_zero has_neg has_add
 -/
#print list.alternating_sum_singleton /- _inst_1: add_comm_group ↝ has_zero has_neg has_add
 -/
#print list.alternating_prod_singleton /- _inst_1: comm_group ↝ has_inv has_one has_mul
 -/
#print list.alternating_prod_cons_cons /- _inst_1: comm_group ↝ has_inv has_one has_mul
 -/
#print list.alternating_sum_cons_cons' /- _inst_1: add_comm_group ↝ has_zero has_neg has_add
 -/
#print list.alternating_sum_cons_cons /- _inst_2: add_comm_group ↝ has_sub has_zero has_neg has_add
 -/
#print list.lex.is_strict_total_order /- _inst_1: is_strict_total_order' ↝ is_trichotomous is_asymm is_order_connected
 -/
#print list.lex.decidable_rel /- _inst_1: decidable_eq ↝
_inst_2: decidable_rel ↝
 -/
#print list.count_nil /- _inst_1: decidable_eq ↝
 -/
#print list.count_cons /- _inst_1: decidable_eq ↝
 -/
#print list.count_cons' /- _inst_1: decidable_eq ↝
 -/
#print list.count_cons_self /- _inst_1: decidable_eq ↝
 -/
#print list.count_cons_of_ne /- _inst_1: decidable_eq ↝
 -/
#print list.count_tail /- _inst_1: decidable_eq ↝
 -/
#print list.count_le_of_sublist /- _inst_1: decidable_eq ↝
 -/
#print list.count_le_count_cons /- _inst_1: decidable_eq ↝
 -/
#print list.count_singleton /- _inst_1: decidable_eq ↝
 -/
#print list.count_append /- _inst_1: decidable_eq ↝
 -/
#print list.count_concat /- _inst_1: decidable_eq ↝
 -/
#print list.count_pos /- _inst_1: decidable_eq ↝
 -/
#print list.count_eq_zero_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print list.not_mem_of_count_eq_zero /- _inst_1: decidable_eq ↝
 -/
#print list.count_repeat /- _inst_1: decidable_eq ↝
 -/
#print list.le_count_iff_repeat_sublist /- _inst_1: decidable_eq ↝
 -/
#print list.repeat_count_eq_of_count_eq_length /- _inst_1: decidable_eq ↝
 -/
#print list.count_filter /- _inst_1: decidable_eq ↝
 -/
#print list.decidable_prefix /- _inst_1: decidable_eq ↝
 -/
#print list.decidable_suffix /- _inst_1: decidable_eq ↝
 -/
#print list.decidable_infix /- _inst_1: decidable_eq ↝
 -/
#print list.insert_nil /- _inst_1: decidable_eq ↝ has_insert
 -/
#print list.insert.def /- _inst_1: decidable_eq ↝
 -/
#print list.insert_of_mem /- _inst_1: decidable_eq ↝
 -/
#print list.insert_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print list.mem_insert_iff /- _inst_1: decidable_eq ↝
 -/
#print list.suffix_insert /- _inst_1: decidable_eq ↝
 -/
#print list.mem_insert_self /- _inst_1: decidable_eq ↝
 -/
#print list.mem_insert_of_mem /- _inst_1: decidable_eq ↝
 -/
#print list.eq_or_mem_of_mem_insert /- _inst_1: decidable_eq ↝
 -/
#print list.length_insert_of_mem /- _inst_1: decidable_eq ↝
 -/
#print list.length_insert_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print list.erase_nil /- _inst_1: decidable_eq ↝
 -/
#print list.erase_cons /- _inst_1: decidable_eq ↝
 -/
#print list.erase_cons_head /- _inst_1: decidable_eq ↝
 -/
#print list.erase_cons_tail /- _inst_1: decidable_eq ↝
 -/
#print list.erase_eq_erasep /- _inst_1: decidable_eq ↝
 -/
#print list.erase_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print list.exists_erase_eq /- _inst_1: decidable_eq ↝
 -/
#print list.length_erase_of_mem /- _inst_1: decidable_eq ↝
 -/
#print list.erase_append_left /- _inst_1: decidable_eq ↝
 -/
#print list.erase_append_right /- _inst_1: decidable_eq ↝
 -/
#print list.erase_sublist /- _inst_1: decidable_eq ↝
 -/
#print list.erase_subset /- _inst_1: decidable_eq ↝
 -/
#print list.sublist.erase /- _inst_1: decidable_eq ↝
 -/
#print list.mem_of_mem_erase /- _inst_1: decidable_eq ↝
 -/
#print list.mem_erase_of_ne /- _inst_1: decidable_eq ↝
 -/
#print list.erase_comm /- _inst_1: decidable_eq ↝
 -/
#print list.map_erase /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print list.map_foldl_erase /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print list.count_erase_self /- _inst_1: decidable_eq ↝
 -/
#print list.count_erase_of_ne /- _inst_1: decidable_eq ↝
 -/
#print list.diff_nil /- _inst_1: decidable_eq ↝
 -/
#print list.diff_cons /- _inst_1: decidable_eq ↝
 -/
#print list.nil_diff /- _inst_1: decidable_eq ↝
 -/
#print list.diff_eq_foldl /- _inst_1: decidable_eq ↝
 -/
#print list.diff_append /- _inst_1: decidable_eq ↝
 -/
#print list.map_diff /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print list.diff_sublist /- _inst_1: decidable_eq ↝
 -/
#print list.diff_subset /- _inst_1: decidable_eq ↝
 -/
#print list.mem_diff_of_mem /- _inst_1: decidable_eq ↝
 -/
#print list.sublist.diff_right /- _inst_1: decidable_eq ↝
 -/
#print list.erase_diff_erase_sublist_of_sublist /- _inst_1: decidable_eq ↝
 -/
#print list.nil_union /- _inst_1: decidable_eq ↝
 -/
#print list.cons_union /- _inst_1: decidable_eq ↝
 -/
#print list.mem_union /- _inst_1: decidable_eq ↝
 -/
#print list.mem_union_left /- _inst_1: decidable_eq ↝
 -/
#print list.mem_union_right /- _inst_1: decidable_eq ↝
 -/
#print list.sublist_suffix_of_union /- _inst_1: decidable_eq ↝
 -/
#print list.suffix_union_right /- _inst_1: decidable_eq ↝
 -/
#print list.union_sublist_append /- _inst_1: decidable_eq ↝
 -/
#print list.forall_mem_union /- _inst_1: decidable_eq ↝
 -/
#print list.forall_mem_of_forall_mem_union_left /- _inst_1: decidable_eq ↝
 -/
#print list.forall_mem_of_forall_mem_union_right /- _inst_1: decidable_eq ↝
 -/
#print list.inter_nil /- _inst_1: decidable_eq ↝
 -/
#print list.inter_cons_of_mem /- _inst_1: decidable_eq ↝
 -/
#print list.inter_cons_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print list.mem_of_mem_inter_left /- _inst_1: decidable_eq ↝
 -/
#print list.mem_of_mem_inter_right /- _inst_1: decidable_eq ↝
 -/
#print list.mem_inter_of_mem_of_mem /- _inst_1: decidable_eq ↝
 -/
#print list.mem_inter /- _inst_1: decidable_eq ↝
 -/
#print list.inter_subset_left /- _inst_1: decidable_eq ↝
 -/
#print list.inter_subset_right /- _inst_1: decidable_eq ↝
 -/
#print list.subset_inter /- _inst_1: decidable_eq ↝
 -/
#print list.inter_eq_nil_iff_disjoint /- _inst_1: decidable_eq ↝
 -/
#print list.forall_mem_inter_of_forall_left /- _inst_1: decidable_eq ↝
 -/
#print list.forall_mem_inter_of_forall_right /- _inst_1: decidable_eq ↝
 -/
#print list.inter_reverse /- _inst_1: decidable_eq ↝
 -/

-- data\list\defs.lean
#print list.has_sdiff /- _inst_1: decidable_eq ↝
 -/
#print list.split_on /- _inst_1: decidable_eq ↝
 -/
#print list.indexes_of /- _inst_1: decidable_eq ↝
 -/
#print list.mfoldl_with_index /- _inst_1: monad ↝ has_pure has_bind
 -/
#print list.mfoldr_with_index /- _inst_1: monad ↝ has_pure has_bind
 -/
#print list.count /- _inst_1: decidable_eq ↝
 -/
#print list.decidable_pairwise /- _inst_1: decidable_rel ↝
 -/
#print list.pw_filter /- _inst_1: decidable_rel ↝
 -/
#print list.decidable_chain /- _inst_1: decidable_rel ↝
 -/
#print list.decidable_chain' /- _inst_1: decidable_rel ↝
 -/
#print list.nodup_decidable /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup /- _inst_1: decidable_eq ↝
 -/
#print list.get_rest /- _inst_1: decidable_eq ↝
 -/

-- data\list\erase_dup.lean
#print list.erase_dup_nil /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup_cons_of_mem' /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup_cons_of_not_mem' /- _inst_1: decidable_eq ↝
 -/
#print list.mem_erase_dup /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup_cons_of_mem /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup_cons_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup_sublist /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup_subset /- _inst_1: decidable_eq ↝
 -/
#print list.subset_erase_dup /- _inst_1: decidable_eq ↝
 -/
#print list.nodup_erase_dup /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup_eq_self /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup_idempotent /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dup_append /- _inst_1: decidable_eq ↝
 -/

-- data\list\forall2.lean
#print list.rel_sum /- _inst_1: add_monoid ↝ has_zero has_add
_inst_2: add_monoid ↝ has_zero has_add
 -/
#print list.rel_prod /- _inst_1: monoid ↝ has_one has_mul
_inst_2: monoid ↝ has_one has_mul
 -/

-- data\list\min_max.lean
#print list.index_of_argmax /- _inst_2: decidable_eq ↝
 -/
#print list.index_of_argmin /- _inst_2: decidable_eq ↝
 -/
#print list.mem_argmax_iff /- _inst_2: decidable_eq ↝
 -/
#print list.argmax_eq_some_iff /- _inst_2: decidable_eq ↝
 -/
#print list.mem_argmin_iff /- _inst_2: decidable_eq ↝
 -/
#print list.argmin_eq_some_iff /- _inst_2: decidable_eq ↝
 -/

-- data\list\nodup.lean
#print list.nth_le_index_of /- _inst_1: decidable_eq ↝
 -/
#print list.nodup_iff_count_le_one /- _inst_1: decidable_eq ↝
 -/
#print list.count_eq_one_of_mem /- _inst_1: decidable_eq ↝
 -/
#print list.nodup_erase_eq_filter /- _inst_1: decidable_eq ↝
 -/
#print list.nodup_erase_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print list.nodup_diff /- _inst_1: decidable_eq ↝
 -/
#print list.mem_erase_iff_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print list.mem_erase_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print list.nodup_insert /- _inst_1: decidable_eq ↝
 -/
#print list.nodup_union /- _inst_1: decidable_eq ↝
 -/
#print list.nodup_inter_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print list.diff_eq_filter_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print list.mem_diff_iff_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print list.nodup.map_update /- _inst_1: decidable_eq ↝
 -/

-- data\list\pairwise.lean
#print list.pw_filter_nil /- _inst_1: decidable_rel ↝
 -/
#print list.pw_filter_cons_of_pos /- _inst_1: decidable_rel ↝
 -/
#print list.pw_filter_cons_of_neg /- _inst_1: decidable_rel ↝
 -/
#print list.pw_filter_map /- _inst_1: decidable_rel ↝
 -/
#print list.pw_filter_sublist /- _inst_1: decidable_rel ↝
 -/
#print list.pw_filter_subset /- _inst_1: decidable_rel ↝
 -/
#print list.pairwise_pw_filter /- _inst_1: decidable_rel ↝
 -/
#print list.pw_filter_eq_self /- _inst_1: decidable_rel ↝
 -/
#print list.pw_filter_idempotent /- _inst_1: decidable_rel ↝
 -/
#print list.forall_mem_pw_filter /- _inst_1: decidable_rel ↝
 -/

-- data\list\palindrome.lean
#print palindrome.decidable /- _inst_1: decidable_eq ↝
 -/

-- data\list\perm.lean
#print list.perm_cons_erase /- _inst_1: decidable_eq ↝
 -/
#print list.perm.count_eq /- _inst_1: decidable_eq ↝
 -/
#print list.subperm.count_le /- _inst_1: decidable_eq ↝
 -/
#print list.perm.sum_eq' /- _inst_1: add_monoid ↝ add_semigroup has_zero
 -/
#print list.perm.prod_eq' /- _inst_1: monoid ↝ semigroup has_one
 -/
#print list.perm.sum_eq /- _inst_1: add_comm_monoid ↝ has_zero is_commutative has_add is_associative
 -/
#print list.perm.prod_eq /- _inst_1: comm_monoid ↝ has_one is_commutative is_associative has_mul
 -/
#print list.perm.erase /- _inst_1: decidable_eq ↝
 -/
#print list.subperm_cons_erase /- _inst_1: decidable_eq ↝
 -/
#print list.erase_subperm /- _inst_1: decidable_eq ↝
 -/
#print list.subperm.erase /- _inst_1: decidable_eq ↝
 -/
#print list.perm.diff_right /- _inst_1: decidable_eq ↝
 -/
#print list.perm.diff_left /- _inst_1: decidable_eq ↝
 -/
#print list.perm.diff /- _inst_1: decidable_eq ↝
 -/
#print list.subperm.diff_right /- _inst_1: decidable_eq ↝
 -/
#print list.erase_cons_subperm_cons_erase /- _inst_1: decidable_eq ↝
 -/
#print list.subperm_cons_diff /- _inst_1: decidable_eq ↝
 -/
#print list.subset_cons_diff /- _inst_1: decidable_eq ↝
 -/
#print list.perm.bag_inter_right /- _inst_1: decidable_eq ↝
 -/
#print list.perm.bag_inter_left /- _inst_1: decidable_eq ↝
 -/
#print list.perm.bag_inter /- _inst_1: decidable_eq ↝
 -/
#print list.cons_perm_iff_perm_erase /- _inst_1: decidable_eq ↝
 -/
#print list.perm_iff_count /- _inst_1: decidable_eq ↝
 -/
#print list.decidable_perm /- _inst_1: decidable_eq ↝
 -/
#print list.perm.erase_dup /- _inst_1: decidable_eq ↝
 -/
#print list.perm.insert /- _inst_1: decidable_eq ↝
 -/
#print list.perm_insert_swap /- _inst_1: decidable_eq ↝
 -/
#print list.perm.union_right /- _inst_1: decidable_eq ↝
 -/
#print list.perm.union_left /- _inst_1: decidable_eq ↝
 -/
#print list.perm.union /- _inst_1: decidable_eq ↝
 -/
#print list.perm.inter_right /- _inst_1: decidable_eq ↝
 -/
#print list.perm.inter_left /- _inst_1: decidable_eq ↝
 -/
#print list.perm.inter /- _inst_1: decidable_eq ↝
 -/
#print list.perm.inter_append /- _inst_1: decidable_eq ↝
 -/
#print list.perm.take_inter /- _inst_1: decidable_eq ↝
 -/
#print list.perm.drop_inter /- _inst_1: decidable_eq ↝
 -/
#print list.perm.slice_inter /- _inst_1: decidable_eq ↝
 -/

-- data\list\sigma.lean
#print list.lookup /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_nil /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_cons_eq /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_cons_ne /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_is_some /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_eq_none /- _inst_1: decidable_eq ↝
 -/
#print list.of_mem_lookup /- _inst_1: decidable_eq ↝
 -/
#print list.mem_lookup /- _inst_1: decidable_eq ↝
 -/
#print list.map_lookup_eq_find /- _inst_1: decidable_eq ↝
 -/
#print list.mem_lookup_iff /- _inst_1: decidable_eq ↝
 -/
#print list.perm_lookup /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_ext /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_all /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_all_nil /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_all_cons_eq /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_all_cons_ne /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_all_eq_nil /- _inst_1: decidable_eq ↝
 -/
#print list.head_lookup_all /- _inst_1: decidable_eq ↝
 -/
#print list.mem_lookup_all /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_all_sublist /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_all_length_le_one /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_all_eq_lookup /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_all_nodup /- _inst_1: decidable_eq ↝
 -/
#print list.perm_lookup_all /- _inst_1: decidable_eq ↝
 -/
#print list.kreplace /- _inst_1: decidable_eq ↝
 -/
#print list.kreplace_of_forall_not /- _inst_1: decidable_eq ↝
 -/
#print list.kreplace_self /- _inst_1: decidable_eq ↝
 -/
#print list.keys_kreplace /- _inst_1: decidable_eq ↝
 -/
#print list.kreplace_nodupkeys /- _inst_1: decidable_eq ↝
 -/
#print list.perm.kreplace /- _inst_1: decidable_eq ↝
 -/
#print list.kerase /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_nil /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_cons_eq /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_cons_ne /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_of_not_mem_keys /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_sublist /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_keys_subset /- _inst_1: decidable_eq ↝
 -/
#print list.mem_keys_of_mem_keys_kerase /- _inst_1: decidable_eq ↝
 -/
#print list.exists_of_kerase /- _inst_1: decidable_eq ↝
 -/
#print list.mem_keys_kerase_of_ne /- _inst_1: decidable_eq ↝
 -/
#print list.keys_kerase /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_kerase /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_nodupkeys /- _inst_1: decidable_eq ↝
 -/
#print list.perm.kerase /- _inst_1: decidable_eq ↝
 -/
#print list.not_mem_keys_kerase /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_kerase /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_kerase_ne /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_append_left /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_append_right /- _inst_1: decidable_eq ↝
 -/
#print list.kerase_comm /- _inst_1: decidable_eq ↝
 -/
#print list.sizeof_kerase /- _inst_2: decidable_eq ↝
 -/
#print list.kinsert /- _inst_1: decidable_eq ↝
 -/
#print list.kinsert_def /- _inst_1: decidable_eq ↝
 -/
#print list.mem_keys_kinsert /- _inst_1: decidable_eq ↝
 -/
#print list.kinsert_nodupkeys /- _inst_1: decidable_eq ↝
 -/
#print list.perm.kinsert /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_kinsert /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_kinsert_ne /- _inst_1: decidable_eq ↝
 -/
#print list.kextract /- _inst_1: decidable_eq ↝
 -/
#print list.kextract_eq_lookup_kerase /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dupkeys /- _inst_1: decidable_eq ↝
 -/
#print list.erase_dupkeys_cons /- _inst_1: decidable_eq ↝
 -/
#print list.nodupkeys_erase_dupkeys /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_erase_dupkeys /- _inst_1: decidable_eq ↝
 -/
#print list.sizeof_erase_dupkeys /- _inst_2: decidable_eq ↝
 -/
#print list.kunion /- _inst_1: decidable_eq ↝
 -/
#print list.nil_kunion /- _inst_1: decidable_eq ↝
 -/
#print list.kunion_nil /- _inst_1: decidable_eq ↝
 -/
#print list.kunion_cons /- _inst_1: decidable_eq ↝
 -/
#print list.mem_keys_kunion /- _inst_1: decidable_eq ↝
 -/
#print list.kunion_kerase /- _inst_1: decidable_eq ↝
 -/
#print list.kunion_nodupkeys /- _inst_1: decidable_eq ↝
 -/
#print list.perm.kunion_right /- _inst_1: decidable_eq ↝
 -/
#print list.perm.kunion_left /- _inst_1: decidable_eq ↝
 -/
#print list.perm.kunion /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_kunion_left /- _inst_1: decidable_eq ↝
 -/
#print list.lookup_kunion_right /- _inst_1: decidable_eq ↝
 -/
#print list.mem_lookup_kunion /- _inst_1: decidable_eq ↝
 -/
#print list.mem_lookup_kunion_middle /- _inst_1: decidable_eq ↝
 -/

-- data\list\sort.lean
#print list.decidable_sorted /- _inst_1: decidable_rel ↝
 -/
#print list.ordered_insert /- _inst_1: decidable_rel ↝
 -/
#print list.insertion_sort /- _inst_1: decidable_rel ↝
 -/
#print list.ordered_insert_nil /- _inst_1: decidable_rel ↝
 -/
#print list.ordered_insert_length /- _inst_1: decidable_rel ↝
 -/
#print list.perm_ordered_insert /- _inst_1: decidable_rel ↝
 -/
#print list.ordered_insert_count /- _inst_1: decidable_rel ↝
_inst_2: decidable_eq ↝
 -/
#print list.perm_insertion_sort /- _inst_1: decidable_rel ↝
 -/
#print list.sorted_ordered_insert /- _inst_1: decidable_rel ↝
_inst_2: is_total ↝
 -/
#print list.sorted_insertion_sort /- _inst_1: decidable_rel ↝
_inst_2: is_total ↝
 -/
#print list.merge /- _inst_1: decidable_rel ↝
 -/
#print list.merge_sort /- _inst_1: decidable_rel ↝
 -/
#print list.merge_sort_cons_cons /- _inst_1: decidable_rel ↝
 -/
#print list.perm_merge /- _inst_1: decidable_rel ↝
 -/
#print list.perm_merge_sort /- _inst_1: decidable_rel ↝
 -/
#print list.length_merge_sort /- _inst_1: decidable_rel ↝
 -/
#print list.sorted_merge /- _inst_1: decidable_rel ↝
_inst_2: is_total ↝
 -/
#print list.sorted_merge_sort /- _inst_1: decidable_rel ↝
_inst_2: is_total ↝
 -/
#print list.merge_sort_eq_self /- _inst_1: decidable_rel ↝
_inst_2: is_total ↝
 -/

-- data\matrix\basic.lean
#print matrix /- _inst_1: fintype ↝
_inst_2: fintype ↝
 -/
#print matrix.diagonal /- _inst_5: decidable_eq ↝
 -/
#print matrix.diagonal_apply_eq /- _inst_5: decidable_eq ↝
 -/
#print matrix.diagonal_apply_ne /- _inst_5: decidable_eq ↝
 -/
#print matrix.diagonal_apply_ne' /- _inst_5: decidable_eq ↝
 -/
#print matrix.diagonal_zero /- _inst_5: decidable_eq ↝
 -/
#print matrix.diagonal_transpose /- _inst_5: decidable_eq ↝
 -/
#print matrix.diagonal_add /- _inst_5: decidable_eq ↝
 -/
#print matrix.diagonal_map /- _inst_5: decidable_eq ↝
 -/
#print matrix.has_one /- _inst_5: decidable_eq ↝
 -/
#print matrix.diagonal_one /- _inst_5: decidable_eq ↝
 -/
#print matrix.one_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix.one_apply_eq /- _inst_5: decidable_eq ↝
 -/
#print matrix.one_apply_ne /- _inst_5: decidable_eq ↝
 -/
#print matrix.one_apply_ne' /- _inst_5: decidable_eq ↝
 -/
#print matrix.one_map /- _inst_5: decidable_eq ↝
 -/
#print matrix.bit1_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix.bit1_apply_eq /- _inst_5: decidable_eq ↝
 -/
#print matrix.bit1_apply_ne /- _inst_5: decidable_eq ↝
 -/
#print matrix.dot_product_comm /- _inst_5: comm_semiring ↝ add_comm_monoid comm_semigroup
 -/
#print matrix.dot_product_zero /- _inst_5: semiring ↝ add_comm_monoid mul_zero_class
 -/
#print matrix.zero_dot_product /- _inst_5: semiring ↝ add_comm_monoid mul_zero_class
 -/
#print matrix.add_dot_product /- _inst_5: semiring ↝ add_comm_monoid distrib
 -/
#print matrix.dot_product_add /- _inst_5: semiring ↝ add_comm_monoid distrib
 -/
#print matrix.diagonal_dot_product /- _inst_5: decidable_eq ↝
_inst_6: semiring ↝ add_comm_monoid mul_zero_class
 -/
#print matrix.dot_product_diagonal /- _inst_5: decidable_eq ↝
_inst_6: semiring ↝ add_comm_monoid mul_zero_class
 -/
#print matrix.dot_product_diagonal' /- _inst_5: decidable_eq ↝
_inst_6: semiring ↝ add_comm_monoid mul_zero_class
 -/
#print matrix.dot_product_smul /- _inst_5: comm_semiring ↝ comm_semigroup semiring
 -/
#print matrix.diagonal_neg /- _inst_5: decidable_eq ↝
 -/
#print matrix.diagonal_mul /- _inst_6: decidable_eq ↝
 -/
#print matrix.mul_diagonal /- _inst_6: decidable_eq ↝
 -/
#print matrix.one_mul /- _inst_6: decidable_eq ↝
 -/
#print matrix.mul_one /- _inst_6: decidable_eq ↝
 -/
#print matrix.monoid /- _inst_6: decidable_eq ↝
 -/
#print matrix.semiring /- _inst_6: decidable_eq ↝
 -/
#print matrix.diagonal_mul_diagonal /- _inst_6: decidable_eq ↝
 -/
#print matrix.diagonal_mul_diagonal' /- _inst_6: decidable_eq ↝
 -/
#print matrix.ring_hom_map_one /- _inst_6: decidable_eq ↝
 -/
#print matrix.ring_equiv_map_one /- _inst_6: decidable_eq ↝
 -/
#print matrix.zero_hom_map_zero /- _inst_5: semiring ↝ has_zero
 -/
#print matrix.add_monoid_hom_map_zero /- _inst_5: semiring ↝ add_monoid
 -/
#print matrix.add_equiv_map_zero /- _inst_5: semiring ↝ add_monoid
 -/
#print matrix.linear_map_map_zero /- _inst_5: semiring ↝ add_comm_monoid
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print matrix.linear_equiv_map_zero /- _inst_5: semiring ↝ add_comm_monoid
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print matrix.row_mul_col_apply /- _inst_5: semiring ↝ add_comm_monoid has_mul
 -/
#print ring_hom.map_matrix /- _inst_5: decidable_eq ↝
 -/
#print ring_hom.map_matrix_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix.ring /- _inst_5: decidable_eq ↝
 -/
#print matrix.has_scalar /- _inst_5: semiring ↝ has_scalar
 -/
#print matrix.semimodule /- _inst_7: semimodule ↝
 -/
#print matrix.smul_apply /- _inst_5: semiring ↝ has_mul
 -/
#print matrix.smul_eq_diagonal_mul /- _inst_6: decidable_eq ↝
 -/
#print matrix.scalar /- _inst_6: decidable_eq ↝
 -/
#print matrix.coe_scalar /- _inst_6: decidable_eq ↝
 -/
#print matrix.scalar_apply_eq /- _inst_6: decidable_eq ↝
 -/
#print matrix.scalar_apply_ne /- _inst_6: decidable_eq ↝
 -/
#print matrix.scalar_inj /- _inst_6: decidable_eq ↝
 -/
#print matrix.smul_eq_mul_diagonal /- _inst_5: comm_semiring ↝ comm_semigroup semiring
_inst_6: decidable_eq ↝
 -/
#print matrix.scalar.commute /- _inst_6: decidable_eq ↝
 -/
#print matrix.mul_vec_diagonal /- _inst_6: decidable_eq ↝
 -/
#print matrix.vec_mul_diagonal /- _inst_6: decidable_eq ↝
 -/
#print matrix.mul_vec_one /- _inst_6: decidable_eq ↝
 -/
#print matrix.vec_mul_one /- _inst_6: decidable_eq ↝
 -/
#print matrix.std_basis_matrix /- _inst_5: semiring ↝ has_zero
_inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.smul_std_basis_matrix /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.std_basis_matrix_zero /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.std_basis_matrix_add /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.matrix_eq_sum_std_basis /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.std_basis_eq_basis_mul_basis /- _inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.induction_on' /- _inst_7: decidable_eq ↝
 -/
#print matrix.induction_on /- _inst_7: decidable_eq ↝
 -/
#print matrix.smul_mul_vec_assoc /- _inst_5: ring ↝ semiring
 -/
#print matrix.transpose_one /- _inst_5: decidable_eq ↝
 -/
#print matrix.transpose_smul /- _inst_5: semiring ↝ has_scalar
 -/
#print matrix.star_ring /- _inst_5: decidable_eq ↝
 -/
#print matrix.star_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix.col_add /- _inst_5: semiring ↝ has_add
 -/
#print matrix.row_add /- _inst_5: semiring ↝ has_add
 -/
#print matrix.update_row /- _inst_5: decidable_eq ↝
 -/
#print matrix.update_column /- _inst_5: decidable_eq ↝
 -/
#print matrix.update_row_self /- _inst_5: decidable_eq ↝
 -/
#print matrix.update_column_self /- _inst_5: decidable_eq ↝
 -/
#print matrix.update_row_ne /- _inst_5: decidable_eq ↝
 -/
#print matrix.update_column_ne /- _inst_5: decidable_eq ↝
 -/
#print matrix.update_row_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix.update_column_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix.update_row_transpose /- _inst_5: decidable_eq ↝
 -/
#print matrix.update_column_transpose /- _inst_5: decidable_eq ↝
 -/
#print matrix.from_blocks_add /- _inst_5: semiring ↝ has_add
 -/
#print matrix.from_blocks_multiply /- _inst_5: semiring ↝ add_comm_monoid has_mul
 -/
#print matrix.from_blocks_diagonal /- _inst_5: semiring ↝ has_zero
_inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.from_blocks_one /- _inst_5: semiring ↝ has_one has_zero
_inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.block_diagonal /- _inst_5: decidable_eq ↝
 -/
#print matrix.block_diagonal_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix.block_diagonal_apply_eq /- _inst_5: decidable_eq ↝
 -/
#print matrix.block_diagonal_apply_ne /- _inst_5: decidable_eq ↝
 -/
#print matrix.block_diagonal_transpose /- _inst_5: decidable_eq ↝
 -/
#print matrix.block_diagonal_zero /- _inst_5: decidable_eq ↝
 -/
#print matrix.block_diagonal_diagonal /- _inst_5: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.block_diagonal_one /- _inst_5: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print matrix.block_diagonal_add /- _inst_5: decidable_eq ↝
 -/
#print matrix.block_diagonal_neg /- _inst_5: decidable_eq ↝
 -/
#print matrix.block_diagonal_sub /- _inst_5: decidable_eq ↝
 -/
#print matrix.block_diagonal_mul /- _inst_5: decidable_eq ↝
_inst_7: semiring ↝ add_comm_monoid mul_zero_class
 -/
#print matrix.block_diagonal_smul /- _inst_5: decidable_eq ↝
_inst_8: semimodule ↝
 -/

-- data\matrix\char_p.lean
#print matrix.char_p /- _inst_2: ring ↝ semiring
_inst_3: decidable_eq ↝
 -/

-- data\matrix\notation.lean
#print matrix.empty_mul /- _inst_4: semiring ↝ add_comm_monoid has_mul
 -/
#print matrix.empty_mul_empty /- _inst_4: semiring ↝ add_comm_monoid has_mul
 -/
#print matrix.mul_empty /- _inst_4: semiring ↝ add_comm_monoid has_mul
 -/
#print matrix.mul_val_succ /- _inst_4: semiring ↝ add_comm_monoid has_mul
 -/
#print matrix.mul_vec_cons /- _inst_5: comm_semiring ↝ comm_semigroup semiring
 -/
#print matrix.smul_empty /- _inst_4: semiring ↝ has_scalar
 -/
#print matrix.smul_mat_empty /- _inst_4: semiring ↝ has_scalar
 -/

-- data\matrix\pequiv.lean
#print pequiv.to_matrix /- _inst_5: decidable_eq ↝
 -/
#print pequiv.mul_matrix_apply /- _inst_5: decidable_eq ↝
_inst_6: semiring ↝ monoid add_comm_monoid mul_zero_class
 -/
#print pequiv.to_matrix_symm /- _inst_5: decidable_eq ↝
_inst_6: decidable_eq ↝
 -/
#print pequiv.to_matrix_refl /- _inst_5: decidable_eq ↝
 -/
#print pequiv.matrix_mul_apply /- _inst_6: decidable_eq ↝
 -/
#print pequiv.to_pequiv_mul_matrix /- _inst_5: decidable_eq ↝
 -/
#print pequiv.to_matrix_trans /- _inst_5: decidable_eq ↝
_inst_6: decidable_eq ↝
 -/
#print pequiv.to_matrix_bot /- _inst_5: decidable_eq ↝
 -/
#print pequiv.to_matrix_injective /- _inst_5: decidable_eq ↝
 -/
#print pequiv.to_matrix_swap /- _inst_5: decidable_eq ↝
_inst_6: ring ↝ has_one add_group
 -/
#print pequiv.single_mul_single /- _inst_5: decidable_eq ↝
_inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print pequiv.single_mul_single_of_ne /- _inst_5: decidable_eq ↝
_inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print pequiv.single_mul_single_right /- _inst_5: decidable_eq ↝
_inst_6: decidable_eq ↝
_inst_7: decidable_eq ↝
 -/
#print pequiv.equiv_to_pequiv_to_matrix /- _inst_5: decidable_eq ↝
 -/

-- data\multiset\antidiagonal.lean
#print multiset.prod_map_add /- _inst_1: comm_semiring ↝ comm_monoid semiring
 -/

-- data\multiset\basic.lean
#print multiset.has_decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print multiset.decidable_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase /- _inst_1: decidable_eq ↝
 -/
#print multiset.coe_erase /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_cons_head /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_cons_tail /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.cons_erase /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_cons_erase /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_add_left_pos /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_add_right_pos /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_add_right_neg /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_add_left_neg /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_le /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_lt /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_subset /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_erase_of_ne /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_of_mem_erase /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_comm /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_le_erase /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_le_iff_le_cons /- _inst_1: decidable_eq ↝
 -/
#print multiset.card_erase_of_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.card_erase_lt_of_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.card_erase_le /- _inst_1: decidable_eq ↝
 -/
#print multiset.sum_map_mul_left /- _inst_1: semiring ↝ add_comm_monoid distrib mul_zero_class
 -/
#print multiset.sum_map_mul_right /- _inst_1: semiring ↝ add_comm_monoid distrib mul_zero_class
 -/
#print multiset.prod_ne_zero /- _inst_1: integral_domain ↝ monoid_with_zero nontrivial comm_monoid no_zero_divisors
 -/
#print multiset.prod_eq_zero /- _inst_1: comm_semiring ↝ comm_monoid mul_zero_class
 -/
#print multiset.prod_eq_zero_iff /- _inst_1: comm_cancel_monoid_with_zero ↝ monoid_with_zero comm_monoid no_zero_divisors
 -/
#print multiset.abs_sum_le_sum_abs /- _inst_1: linear_ordered_field ↝ linear_ordered_add_comm_group
 -/
#print multiset.sub /- _inst_1: decidable_eq ↝
 -/
#print multiset.has_sub /- _inst_1: decidable_eq ↝
 -/
#print multiset.coe_sub /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_eq_fold_erase /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_cons /- _inst_1: decidable_eq ↝
 -/
#print multiset.add_sub_of_le /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_add' /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_add_cancel /- _inst_1: decidable_eq ↝
 -/
#print multiset.add_sub_cancel_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.add_sub_cancel /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_le_sub_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_le_sub_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_le_iff_le_add /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_sub_add /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_le_self /- _inst_1: decidable_eq ↝
 -/
#print multiset.card_sub /- _inst_1: decidable_eq ↝
 -/
#print multiset.union /- _inst_1: decidable_eq ↝
 -/
#print multiset.has_union /- _inst_1: decidable_eq ↝
 -/
#print multiset.union_def /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_union_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_union_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.eq_union_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.union_le_union_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.union_le /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_union /- _inst_1: decidable_eq ↝
 -/
#print multiset.map_union /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print multiset.inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.has_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.inter_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.zero_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.cons_inter_of_pos /- _inst_1: decidable_eq ↝
 -/
#print multiset.cons_inter_of_neg /- _inst_1: decidable_eq ↝
 -/
#print multiset.inter_le_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.inter_le_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.lattice /- _inst_1: decidable_eq ↝
 -/
#print multiset.sup_eq_union /- _inst_1: decidable_eq ↝
 -/
#print multiset.inf_eq_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_inter_iff /- _inst_1: decidable_eq ↝
 -/
#print multiset.union_le_iff /- _inst_1: decidable_eq ↝
 -/
#print multiset.semilattice_inf_bot /- _inst_1: decidable_eq ↝
 -/
#print multiset.union_comm /- _inst_1: decidable_eq ↝
 -/
#print multiset.inter_comm /- _inst_1: decidable_eq ↝
 -/
#print multiset.eq_union_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.union_le_union_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.union_le_add /- _inst_1: decidable_eq ↝
 -/
#print multiset.union_add_distrib /- _inst_1: decidable_eq ↝
 -/
#print multiset.add_union_distrib /- _inst_1: decidable_eq ↝
 -/
#print multiset.cons_union_distrib /- _inst_1: decidable_eq ↝
 -/
#print multiset.inter_add_distrib /- _inst_1: decidable_eq ↝
 -/
#print multiset.add_inter_distrib /- _inst_1: decidable_eq ↝
 -/
#print multiset.cons_inter_distrib /- _inst_1: decidable_eq ↝
 -/
#print multiset.union_add_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_add_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.sub_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.filter_sub /- _inst_2: decidable_eq ↝
 -/
#print multiset.filter_union /- _inst_2: decidable_eq ↝
 -/
#print multiset.filter_inter /- _inst_2: decidable_eq ↝
 -/
#print multiset.countp_sub /- _inst_2: decidable_eq ↝
 -/
#print multiset.count /- _inst_1: decidable_eq ↝
 -/
#print multiset.coe_count /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_cons_self /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_cons_of_ne /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_le_of_le /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_le_count_cons /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_cons /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_singleton /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_add /- _inst_1: decidable_eq ↝
 -/
#print multiset.count.is_add_monoid_hom /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_smul /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_pos /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_eq_zero_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_eq_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_ne_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_repeat_self /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_repeat /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_erase_self /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_erase_of_ne /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_sub /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_union /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_sum /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_bind /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_count_iff_repeat_le /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_filter_of_pos /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_filter_of_neg /- _inst_1: decidable_eq ↝
 -/
#print multiset.ext /- _inst_1: decidable_eq ↝
 -/
#print multiset.ext' /- _inst_1: decidable_eq ↝
 -/
#print multiset.coe_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_iff_count /- _inst_1: decidable_eq ↝
 -/
#print multiset.distrib_lattice /- _inst_1: decidable_eq ↝
 -/
#print multiset.semilattice_sup_bot /- _inst_1: decidable_eq ↝
 -/
#print multiset.inter_eq_zero_iff_disjoint /- _inst_1: decidable_eq ↝
 -/
#print multiset.disjoint_union_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.disjoint_union_right /- _inst_1: decidable_eq ↝
 -/

-- data\multiset\erase_dup.lean
#print multiset.erase_dup /- _inst_1: decidable_eq ↝
 -/
#print multiset.coe_erase_dup /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_erase_dup /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_cons_of_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_cons_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_le /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_subset /- _inst_1: decidable_eq ↝
 -/
#print multiset.subset_erase_dup /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_subset' /- _inst_1: decidable_eq ↝
 -/
#print multiset.subset_erase_dup' /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_erase_dup /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_eq_self /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_eq_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_singleton /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_erase_dup /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_ext /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_map_erase_dup_eq /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print multiset.erase_dup_nsmul /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup.le_erase_dup_iff_le /- _inst_1: decidable_eq ↝
 -/

-- data\multiset\finset_ops.lean
#print multiset.ndinsert /- _inst_1: decidable_eq ↝
 -/
#print multiset.coe_ndinsert /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinsert_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinsert_of_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinsert_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_ndinsert /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_ndinsert_self /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_ndinsert_self /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_ndinsert_of_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.length_ndinsert_of_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.length_ndinsert_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_cons /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_ndinsert /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinsert_le /- _inst_1: decidable_eq ↝
 -/
#print multiset.attach_ndinsert /- _inst_1: decidable_eq ↝
 -/
#print multiset.disjoint_ndinsert_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.disjoint_ndinsert_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndunion /- _inst_1: decidable_eq ↝
 -/
#print multiset.coe_ndunion /- _inst_1: decidable_eq ↝
 -/
#print multiset.zero_ndunion /- _inst_1: decidable_eq ↝
 -/
#print multiset.cons_ndunion /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_ndunion /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_ndunion_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.subset_ndunion_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndunion_le_add /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndunion_le /- _inst_1: decidable_eq ↝
 -/
#print multiset.subset_ndunion_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_ndunion_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndunion_le_union /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_ndunion /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndunion_eq_union /- _inst_1: decidable_eq ↝
 -/
#print multiset.erase_dup_add /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinter /- _inst_1: decidable_eq ↝
 -/
#print multiset.coe_ndinter /- _inst_1: decidable_eq ↝
 -/
#print multiset.zero_ndinter /- _inst_1: decidable_eq ↝
 -/
#print multiset.cons_ndinter_of_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinter_cons_of_not_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_ndinter /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_ndinter /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_ndinter /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinter_le_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinter_subset_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinter_subset_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinter_le_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.inter_le_ndinter /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinter_eq_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.ndinter_eq_zero_iff_disjoint /- _inst_1: decidable_eq ↝
 -/

-- data\multiset\fold.lean
#print multiset.fold_union_inter /- _inst_1: decidable_eq ↝
 -/
#print multiset.fold_erase_dup_idem /- _inst_1: decidable_eq ↝
 -/
#print multiset.le_smul_erase_dup /- _inst_1: decidable_eq ↝
 -/

-- data\multiset\gcd.lean
#print multiset.lcm_erase_dup /- _inst_4: decidable_eq ↝
 -/
#print multiset.lcm_ndunion /- _inst_4: decidable_eq ↝
 -/
#print multiset.lcm_union /- _inst_4: decidable_eq ↝
 -/
#print multiset.lcm_ndinsert /- _inst_4: decidable_eq ↝
 -/
#print multiset.gcd_erase_dup /- _inst_4: decidable_eq ↝
 -/
#print multiset.gcd_ndunion /- _inst_4: decidable_eq ↝
 -/
#print multiset.gcd_union /- _inst_4: decidable_eq ↝
 -/
#print multiset.gcd_ndinsert /- _inst_4: decidable_eq ↝
 -/

-- data\multiset\lattice.lean
#print multiset.sup_erase_dup /- _inst_2: decidable_eq ↝
 -/
#print multiset.sup_ndunion /- _inst_2: decidable_eq ↝
 -/
#print multiset.sup_union /- _inst_2: decidable_eq ↝
 -/
#print multiset.sup_ndinsert /- _inst_2: decidable_eq ↝
 -/
#print multiset.inf_erase_dup /- _inst_2: decidable_eq ↝
 -/
#print multiset.inf_ndunion /- _inst_2: decidable_eq ↝
 -/
#print multiset.inf_union /- _inst_2: decidable_eq ↝
 -/
#print multiset.inf_ndinsert /- _inst_2: decidable_eq ↝
 -/

-- data\multiset\nodup.lean
#print multiset.nodup_iff_count_le_one /- _inst_1: decidable_eq ↝
 -/
#print multiset.count_eq_one_of_mem /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_decidable /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_erase_eq_filter /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_erase_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_erase_iff_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_erase_of_nodup /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_inter_left /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_inter_right /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_union /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_sub_of_nodup /- _inst_1: decidable_eq ↝
 -/

-- data\multiset\pi.lean
#print multiset.pi.cons /- _inst_1: decidable_eq ↝
 -/
#print multiset.pi.cons_same /- _inst_1: decidable_eq ↝
 -/
#print multiset.pi.cons_ne /- _inst_1: decidable_eq ↝
 -/
#print multiset.pi.cons_swap /- _inst_1: decidable_eq ↝
 -/
#print multiset.pi /- _inst_1: decidable_eq ↝
 -/
#print multiset.pi_zero /- _inst_1: decidable_eq ↝
 -/
#print multiset.pi_cons /- _inst_1: decidable_eq ↝
 -/
#print multiset.pi_cons_injective /- _inst_1: decidable_eq ↝
 -/
#print multiset.card_pi /- _inst_1: decidable_eq ↝
 -/
#print multiset.nodup_pi /- _inst_1: decidable_eq ↝
 -/
#print multiset.mem_pi /- _inst_1: decidable_eq ↝
 -/

-- data\multiset\powerset.lean
#print multiset.revzip_powerset_aux_lemma /- _inst_1: decidable_eq ↝
 -/

-- data\multiset\sections.lean
#print multiset.prod_map_sum /- _inst_1: comm_semiring ↝ comm_monoid semiring
 -/

-- data\multiset\sort.lean
#print multiset.sort /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print multiset.coe_sort /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print multiset.sort_sorted /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print multiset.sort_eq /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print multiset.mem_sort /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/
#print multiset.length_sort /- _inst_1: decidable_rel ↝
_inst_4: is_total ↝
 -/

-- data\mv_polynomial\basic.lean
#print mv_polynomial /- _inst_1: comm_semiring ↝ semiring
 -/
#print mv_polynomial.decidable_eq_mv_polynomial /- _inst_2: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print mv_polynomial.alg_hom_ext /- _inst_2: comm_semiring ↝ semiring
 -/
#print mv_polynomial.eval₂ /- _inst_2: comm_semiring ↝ comm_monoid semiring
 -/

-- data\mv_polynomial\comm_ring.lean
#print mv_polynomial.eval₂_sub /- _inst_2: comm_ring ↝ ring comm_semiring
 -/
#print mv_polynomial.eval₂_neg /- _inst_2: comm_ring ↝ ring comm_semiring
 -/
#print mv_polynomial.hom_C /- _inst_2: comm_ring ↝ ring
 -/

-- data\mv_polynomial\counit.lean
#print mv_polynomial.counit /- _inst_3: comm_ring ↝ ring comm_semiring
 -/

-- data\mv_polynomial\variables.lean
#print mv_polynomial.vars_C_mul /- _inst_2: integral_domain ↝ no_zero_divisors comm_semiring
 -/

-- data\nat\cast.lean
#print nat.cast_two /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print nat.cast_dvd /- _inst_1: field ↝ comm_group_with_zero semiring
 -/
#print nat.cast_commute /- _inst_1: semiring ↝ monoid distrib mul_zero_class
 -/
#print nat.strict_mono_cast /- _inst_1: linear_ordered_semiring ↝ nontrivial ordered_semiring
 -/
#print nat.abs_cast /- _inst_1: linear_ordered_comm_ring ↝ linear_ordered_add_comm_group linear_ordered_semiring
 -/

-- data\nat\choose\sum.lean
#print add_pow /- _inst_1: comm_semiring ↝ comm_semigroup semiring
 -/
#print finset.sum_powerset_neg_one_pow_card /- _inst_1: decidable_eq ↝
 -/

-- data\nat\prime.lean
#print nat.monoid.prime_pow /- _inst_1: monoid ↝ has_pow
 -/

-- data\num\lemmas.lean
#print pos_num.cast_to_int /- _inst_1: add_group ↝ add_monoid has_neg
 -/
#print num.cast_to_int /- _inst_1: add_group ↝ add_monoid has_neg
 -/
#print num.cast_add /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print num.cast_inj /- _inst_1: linear_ordered_semiring ↝ add_monoid char_zero has_one
 -/
#print num.cast_of_znum /- _inst_1: add_group ↝ add_monoid
 -/
#print znum.cast_inj /- _inst_1: linear_ordered_ring ↝ char_zero has_one add_group
 -/

-- data\padics\ring_homs.lean
#print padic_int.nth_hom /- _inst_1: comm_ring ↝ semiring
 -/
#print padic_int.to_zmod_pow_eq_iff_ext /- _inst_1: comm_ring ↝ semiring
 -/

-- data\pequiv.lean
#print pequiv.single /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print pequiv.mem_single /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print pequiv.mem_single_iff /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print pequiv.symm_single /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print pequiv.single_apply /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print pequiv.single_apply_of_ne /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print pequiv.single_trans_of_mem /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print pequiv.trans_single_of_mem /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print pequiv.single_trans_single /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print pequiv.single_subsingleton_eq_refl /- _inst_1: decidable_eq ↝
 -/
#print pequiv.trans_single_of_eq_none /- _inst_2: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print pequiv.single_trans_of_eq_none /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print pequiv.single_trans_single_of_ne /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print pequiv.semilattice_inf_bot /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/

-- data\pfunctor\univariate\M.lean
#print pfunctor.M.ichildren /- _inst_2: decidable_eq ↝
 -/
#print pfunctor.M.isubtree /- _inst_1: decidable_eq ↝
 -/
#print pfunctor.M.iselect /- _inst_1: decidable_eq ↝
 -/
#print pfunctor.M.iselect_eq_default /- _inst_1: decidable_eq ↝
 -/
#print pfunctor.M.ichildren_mk /- _inst_1: decidable_eq ↝
 -/
#print pfunctor.M.isubtree_cons /- _inst_1: decidable_eq ↝
 -/
#print pfunctor.M.iselect_nil /- _inst_1: decidable_eq ↝
 -/
#print pfunctor.M.iselect_cons /- _inst_1: decidable_eq ↝
 -/
#print pfunctor.M.ext_aux /- _inst_2: decidable_eq ↝
 -/

-- data\pfunctor\univariate\basic.lean
#print pfunctor.obj.iget /- _inst_1: decidable_eq ↝
 -/
#print pfunctor.iget_map /- _inst_1: decidable_eq ↝
 -/

-- data\pi.lean
#print pi.single /- _inst_1: decidable_eq ↝
 -/
#print pi.single_eq_same /- _inst_1: decidable_eq ↝
 -/
#print pi.single_eq_of_ne /- _inst_1: decidable_eq ↝
 -/
#print pi.single_injective /- _inst_1: decidable_eq ↝
 -/

-- data\polynomial\algebra_map.lean
#print polynomial.C_eq_algebra_map /- _inst_4: comm_ring ↝ comm_semiring
 -/
#print polynomial.alg_hom_eval₂_algebra_map /- _inst_4: comm_ring ↝ comm_semiring
_inst_5: ring ↝ semiring
_inst_6: ring ↝ semiring
 -/
#print polynomial.eval₂_algebra_map_X /- _inst_5: ring ↝ semiring
 -/
#print polynomial.eval₂_comp /- _inst_1: comm_semiring ↝ semiring
 -/
#print polynomial.is_root_of_eval₂_map_eq_zero /- _inst_6: comm_ring ↝ comm_semiring
 -/
#print polynomial.aeval_eq_sum_range /- _inst_6: comm_ring ↝ comm_semiring
 -/
#print polynomial.aeval_eq_sum_range' /- _inst_6: comm_ring ↝ comm_semiring
 -/
#print polynomial.aeval_endomorphism /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_3: module ↝ algebra
 -/

-- data\polynomial\basic.lean
#print polynomial.semimodule /- _inst_3: semimodule ↝
 -/
#print polynomial.smul_monomial /- _inst_3: semimodule ↝
 -/
#print polynomial.lhom_ext' /- _inst_3: semimodule ↝
 -/

-- data\polynomial\cancel_leads.lean
#print polynomial.cancel_leads /- _inst_1: comm_ring ↝ ring
 -/

-- data\polynomial\degree\definitions.lean
#print polynomial.monic.decidable /- _inst_2: decidable_eq ↝
 -/
#print polynomial.degree_mul /- _inst_1: integral_domain ↝ ring no_zero_divisors
 -/
#print polynomial.leading_coeff_mul /- _inst_1: integral_domain ↝ ring no_zero_divisors
 -/

-- data\polynomial\degree\trailing_degree.lean
#print polynomial.trailing_monic.decidable /- _inst_2: decidable_eq ↝
 -/

-- data\polynomial\derivative.lean
#print polynomial.of_mem_support_derivative /- _inst_1: comm_semiring ↝ semiring
 -/
#print polynomial.mem_support_derivative /- _inst_1: integral_domain ↝ no_zero_divisors semiring
 -/
#print polynomial.nat_degree_eq_zero_of_derivative_eq_zero /- _inst_1: integral_domain ↝ no_zero_divisors semiring
 -/

-- data\polynomial\div.lean
#print polynomial.eval₂_mod_by_monic_eq_self_of_root /- _inst_2: comm_ring ↝ ring comm_semiring
 -/
#print polynomial.multiplicity_X_sub_C_finite /- _inst_1: comm_ring ↝ ring comm_semiring
 -/

-- data\polynomial\eval.lean
#print polynomial.eval₂_mul /- _inst_2: comm_semiring ↝ comm_semigroup semiring
 -/
#print polynomial.eval₂_eq_sum_range /- _inst_2: comm_semiring ↝ semiring
 -/
#print polynomial.eval₂_eq_sum_range' /- _inst_2: comm_semiring ↝ semiring
 -/
#print polynomial.is_root.decidable /- _inst_2: decidable_eq ↝
 -/
#print polynomial.support_map_subset /- _inst_1: comm_semiring ↝ semiring
_inst_2: comm_semiring ↝ semiring
 -/
#print polynomial.eval₂_neg /- _inst_2: ring ↝ add_group semiring
 -/
#print polynomial.eval₂.is_ring_hom /- _inst_1: comm_ring ↝ ring
_inst_2: comm_ring ↝ ring comm_semiring
 -/

-- data\polynomial\field_division.lean
#print polynomial.is_unit_iff_degree_eq_zero /- _inst_1: field ↝ group_with_zero integral_domain
 -/
#print polynomial.degree_pos_of_ne_zero_of_nonunit /- _inst_1: field ↝ group_with_zero ring
 -/
#print polynomial.monic_mul_leading_coeff_inv /- _inst_1: field ↝ group_with_zero integral_domain
 -/
#print polynomial.degree_mul_leading_coeff_inv /- _inst_1: field ↝ group_with_zero integral_domain
 -/
#print polynomial.div /- _inst_1: field ↝ has_inv ring
 -/
#print polynomial.mod /- _inst_1: field ↝ has_inv ring
 -/
#print polynomial.degree_map /- _inst_1: field ↝ division_ring
_inst_2: field ↝ nontrivial semiring
 -/
#print polynomial.map_eq_zero /- _inst_1: field ↝ division_ring
 -/
#print polynomial.mem_roots_map /- _inst_2: field ↝ integral_domain
 -/
#print polynomial.exists_root_of_degree_eq_one /- _inst_1: field ↝ ring comm_group_with_zero comm_semiring
 -/
#print polynomial.coeff_inv_units /- _inst_1: field ↝ division_ring integral_domain
 -/
#print polynomial.monic_normalize /- _inst_1: field ↝ comm_group_with_zero integral_domain
 -/
#print polynomial.coe_norm_unit_of_ne_zero /- _inst_1: field ↝ comm_group_with_zero integral_domain
 -/
#print polynomial.normalize_monic /- _inst_1: field ↝ comm_group_with_zero integral_domain
 -/
#print polynomial.degree_normalize /- _inst_1: field ↝ comm_group_with_zero integral_domain
 -/
#print polynomial.not_irreducible_C /- _inst_1: field ↝ group_with_zero ring comm_semiring
 -/
#print polynomial.pairwise_coprime_X_sub /- _inst_2: field ↝ group_with_zero ring comm_semiring
 -/
#print polynomial.prod_multiset_root_eq_finset_root /- _inst_1: field ↝ integral_domain
 -/
#print polynomial.roots_C_mul /- _inst_1: field ↝ integral_domain
 -/

-- data\polynomial\identities.lean
#print polynomial.derivative_eval /- _inst_1: comm_ring ↝ comm_semiring
 -/

-- data\polynomial\integral_normalization.lean
#print polynomial.support_integral_normalization /- _inst_1: integral_domain ↝ nontrivial no_zero_divisors semiring
 -/
#print polynomial.integral_normalization_eval₂_eq_zero /- _inst_2: comm_ring ↝ comm_monoid semiring
 -/

-- data\polynomial\iterated_deriv.lean
#print polynomial.coeff_iterated_deriv_as_prod_Ico /- _inst_1: comm_semiring ↝ comm_monoid semiring
 -/

-- data\polynomial\monic.lean
#print polynomial.monic.coeff_nat_degree /- _inst_1: comm_ring ↝ semiring
 -/
#print polynomial.monic.degree_eq_zero_iff_eq_one /- _inst_1: comm_ring ↝ ring
 -/
#print polynomial.monic.nat_degree_mul /- _inst_1: comm_ring ↝ ring
 -/
#print polynomial.leading_coeff_of_injective /- _inst_1: ring ↝ semiring
 -/

-- data\polynomial\reverse.lean
#print polynomial.reverse_mul_of_domain /- _inst_2: domain ↝ ring no_zero_divisors
 -/

-- data\polynomial\ring_division.lean
#print polynomial.nat_degree_pos_of_aeval_root /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ semiring
 -/
#print polynomial.root_mul /- _inst_1: integral_domain ↝ ring no_zero_divisors comm_semiring
 -/
#print polynomial.prime_X_sub_C /- _inst_1: integral_domain ↝ nontrivial comm_ring no_zero_divisors
 -/
#print polynomial.root_multiplicity_zero /- _inst_1: integral_domain ↝ comm_ring
 -/
#print polynomial.root_multiplicity_eq_zero /- _inst_1: integral_domain ↝ comm_ring
 -/
#print polynomial.root_multiplicity_pos /- _inst_1: integral_domain ↝ comm_ring
 -/
#print is_integral_domain.polynomial /- _inst_1: comm_ring ↝ ring
 -/

-- data\prod.lean
#print prod.lex.decidable /- _inst_1: decidable_eq ↝
_inst_2: decidable_rel ↝
_inst_3: decidable_rel ↝
 -/

-- data\quaternion.lean
#print quaternion_algebra.has_coe_t /- _inst_1: comm_ring ↝ has_zero
 -/
#print quaternion_algebra.coe_re /- _inst_1: comm_ring ↝ has_coe_t
 -/
#print quaternion_algebra.coe_im_i /- _inst_1: comm_ring ↝ has_coe_t has_zero
 -/
#print quaternion_algebra.coe_im_j /- _inst_1: comm_ring ↝ has_coe_t has_zero
 -/
#print quaternion_algebra.coe_im_k /- _inst_1: comm_ring ↝ has_coe_t has_zero
 -/
#print quaternion_algebra.coe_injective /- _inst_1: comm_ring ↝ has_coe_t
 -/
#print quaternion_algebra.has_zero /- _inst_1: comm_ring ↝ has_zero
 -/
#print quaternion_algebra.has_one /- _inst_1: comm_ring ↝ has_one has_zero
 -/
#print quaternion_algebra.has_add /- _inst_1: comm_ring ↝ has_add
 -/
#print quaternion_algebra.has_neg /- _inst_1: comm_ring ↝ has_neg
 -/
#print quaternion_algebra.has_mul /- _inst_1: comm_ring ↝ has_sub has_add has_mul
 -/
#print quaternion_algebra.conj_fixed /- _inst_2: integral_domain ↝ comm_ring no_zero_divisors
 -/
#print quaternion.has_coe_t /- _inst_1: comm_ring ↝ has_one has_coe_t has_neg
 -/
#print quaternion.ext /- _inst_1: comm_ring ↝ has_one has_neg
 -/
#print quaternion.ext_iff /- _inst_1: comm_ring ↝ has_one has_neg
 -/
#print quaternion.coe_re /- _inst_1: comm_ring ↝ has_one has_coe_t has_neg
 -/
#print quaternion.coe_im_i /- _inst_1: comm_ring ↝ has_one has_coe_t has_zero has_neg
 -/
#print quaternion.coe_im_j /- _inst_1: comm_ring ↝ has_one has_coe_t has_zero has_neg
 -/
#print quaternion.coe_im_k /- _inst_1: comm_ring ↝ has_one has_coe_t has_zero has_neg
 -/
#print quaternion.norm_sq_eq_zero /- _inst_1: linear_ordered_comm_ring ↝ linear_ordered_ring comm_ring
 -/
#print quaternion.norm_sq_nonneg /- _inst_1: linear_ordered_comm_ring ↝ linear_ordered_ring comm_ring
 -/
#print quaternion.has_inv /- _inst_1: linear_ordered_field ↝ has_inv comm_ring
 -/

-- data\rat\cast.lean
#print rat.cast_coe /- _inst_1: division_ring ↝ has_one has_zero has_neg has_add has_div
 -/

-- data\real\cau_seq.lean
#print is_absolute_value.abv_one /- _inst_4: domain ↝ nontrivial ring
 -/
#print is_absolute_value.abv_inv /- _inst_4: field ↝ group_with_zero domain
 -/
#print is_cau_seq /- _inst_1: linear_ordered_field ↝ has_lt has_zero
_inst_2: ring ↝ has_sub
 -/
#print cau_seq.one_not_equiv_zero /- _inst_2: integral_domain ↝ nontrivial ring
 -/

-- data\real\cau_seq_completion.lean
#print cau_seq.completion.Cauchy /- _inst_2: comm_ring ↝ ring
 -/
#print cau_seq.completion.cau_seq_zero_ne_one /- _inst_2: field ↝ nontrivial ring
 -/

-- data\seq\wseq.lean
#print wseq.index_of /- _inst_1: decidable_eq ↝
 -/
#print wseq.indexes_of /- _inst_1: decidable_eq ↝
 -/

-- data\set\finite.lean
#print set.decidable_mem_of_fintype /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_insert /- _inst_1: decidable_eq ↝
 -/
#print set.to_finset_insert /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_union /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_image /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_range /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_map /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_Union /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_bUnion /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_bUnion' /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_image2 /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_bind /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_bind' /- _inst_1: decidable_eq ↝
 -/
#print set.fintype_seq /- _inst_1: decidable_eq ↝
 -/
#print finset.coe_bind /- _inst_1: decidable_eq ↝
 -/

-- data\set\function.lean
#print set.piecewise_insert /- _inst_2: decidable_eq ↝
 -/
#print function.update_comp_eq_of_not_mem_range /- _inst_1: decidable_eq ↝
 -/
#print function.update_comp_eq_of_injective /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/

-- data\set\intervals\basic.lean
#print set.Ioo /- _inst_1: preorder ↝ has_lt
 -/
#print set.Ico /- _inst_1: preorder ↝ has_lt has_le
 -/
#print set.Iio /- _inst_1: preorder ↝ has_lt
 -/
#print set.Icc /- _inst_1: preorder ↝ has_le
 -/
#print set.Iic /- _inst_1: preorder ↝ has_le
 -/
#print set.Ioc /- _inst_1: preorder ↝ has_lt has_le
 -/
#print set.Ici /- _inst_1: preorder ↝ has_le
 -/
#print set.Ioi /- _inst_1: preorder ↝ has_lt
 -/
#print set.Iio_inter_Iio /- _inst_2: is_total ↝
 -/
#print set.Ioi_inter_Ioi /- _inst_2: is_total ↝
 -/
#print set.Icc_inter_Icc /- _inst_1: lattice ↝ semilattice_inf semilattice_sup
 -/
#print set.Ico_inter_Ico /- _inst_1: lattice ↝ semilattice_inf semilattice_sup
ht: is_total ↝
 -/
#print set.Ioc_inter_Ioc /- _inst_1: lattice ↝ semilattice_inf semilattice_sup
ht: is_total ↝
 -/
#print set.Ioo_inter_Ioo /- _inst_1: lattice ↝ semilattice_inf semilattice_sup
ht: is_total ↝
 -/
#print set.nonempty_Ico_sdiff /- _inst_1: linear_ordered_add_comm_group ↝ linear_order ordered_cancel_add_comm_monoid
 -/

-- data\set\intervals\pi.lean
#print set.Icc_diff_pi_univ_Ioo_subset /- _inst_1: decidable_eq ↝
 -/
#print set.Icc_diff_pi_univ_Ioc_subset /- _inst_1: decidable_eq ↝
 -/

-- data\set\intervals\surj_on.lean
#print surj_on_Ioo_of_monotone_surjective /- _inst_2: partial_order ↝ preorder
 -/
#print surj_on_Ioi_of_monotone_surjective /- _inst_2: partial_order ↝ preorder
 -/

-- data\sigma\basic.lean
#print sigma.decidable_eq /- h₁: decidable_eq ↝
 -/
#print psigma.decidable_eq /- h₁: decidable_eq ↝
 -/

-- data\support.lean
#print function.support_inv /- _inst_1: division_ring ↝ group_with_zero
 -/

-- data\sym.lean
#print sym.decidable_mem /- _inst_1: decidable_eq ↝
 -/

-- data\sym2.lean
#print sym2.is_diag.decidable_pred /- _inst_1: decidable_eq ↝
 -/
#print sym2.from_rel.decidable_as_set /- h: decidable_rel ↝
 -/
#print sym2.from_rel.decidable_pred /- h: decidable_rel ↝
 -/
#print sym2.rel_bool /- _inst_1: decidable_eq ↝
 -/
#print sym2.rel_bool_spec /- _inst_1: decidable_eq ↝
 -/
#print sym2.rel.decidable_rel /- _inst_1: decidable_eq ↝
 -/
#print sym2.mem.other' /- _inst_1: decidable_eq ↝
 -/
#print sym2.mem_other_spec' /- _inst_1: decidable_eq ↝
 -/
#print sym2.other_eq_other' /- _inst_1: decidable_eq ↝
 -/
#print sym2.mem_other_mem' /- _inst_1: decidable_eq ↝
 -/
#print sym2.other_invol' /- _inst_1: decidable_eq ↝
 -/

-- data\tree.lean
#print tree.index_of /- _inst_1: decidable_rel ↝
 -/

-- data\vector2.lean
#print vector.traverse_def /- _inst_3: is_lawful_applicative ↝
 -/

-- data\zmod\basic.lean
#print zmod.nat_cast_val /- _inst_1: ring ↝ has_one has_zero has_neg has_add
 -/
#print zmod.cast_one /- _inst_1: ring ↝ has_neg subsingleton semiring
 -/
#print zmod.cast_add /- _inst_1: ring ↝ add_group semiring
 -/
#print zmod.algebra /- _inst_3: comm_ring ↝ ring comm_semiring
 -/

-- data\zsqrtd\gaussian_int.lean
#print gaussian_int.nat_cast_nat_abs_norm /- _inst_1: ring ↝ has_one has_zero has_neg has_add
 -/

-- deprecated\group.lean
#print is_add_hom.add /- _inst_4: add_semigroup ↝ has_add
 -/
#print is_mul_hom.mul /- _inst_4: semigroup ↝ has_mul
 -/
#print add_equiv.is_add_hom /- _inst_1: add_monoid ↝ has_add
_inst_2: add_monoid ↝ has_add
 -/
#print mul_equiv.is_mul_hom /- _inst_1: monoid ↝ has_mul
_inst_2: monoid ↝ has_mul
 -/
#print is_add_monoid_hom.map_add /- _inst_3: is_add_monoid_hom ↝ is_add_hom
 -/
#print is_monoid_hom.map_mul /- _inst_3: is_monoid_hom ↝ is_mul_hom
 -/
#print is_add_monoid_hom.is_add_monoid_hom_mul_left /- _inst_1: semiring ↝ add_monoid distrib mul_zero_class
 -/
#print is_add_monoid_hom.is_add_monoid_hom_mul_right /- _inst_1: semiring ↝ add_monoid distrib mul_zero_class
 -/
#print is_group_hom.to_is_monoid_hom /- _inst_3: is_group_hom ↝ is_mul_hom
 -/
#print is_add_group_hom.to_is_add_monoid_hom /- _inst_3: is_add_group_hom ↝ is_add_hom
 -/
#print is_group_hom.map_one /- _inst_3: is_group_hom ↝ is_monoid_hom
 -/
#print is_add_group_hom.map_zero /- _inst_3: is_add_group_hom ↝ is_add_monoid_hom
 -/
#print is_group_hom.comp /- _inst_3: is_group_hom ↝ is_mul_hom
_inst_5: is_group_hom ↝ is_mul_hom
 -/
#print is_add_group_hom.comp /- _inst_3: is_add_group_hom ↝ is_add_hom
_inst_5: is_add_group_hom ↝ is_add_hom
 -/
#print is_add_group_hom.add /- _inst_5: add_comm_group ↝ add_group
_inst_6: is_add_group_hom ↝ is_add_hom
_inst_7: is_add_group_hom ↝ is_add_hom
 -/
#print is_group_hom.mul /- _inst_5: comm_group ↝ group
_inst_6: is_group_hom ↝ is_mul_hom
_inst_7: is_group_hom ↝ is_mul_hom
 -/
#print is_group_hom.inv /- _inst_5: comm_group ↝ group
_inst_6: is_group_hom ↝ is_mul_hom
 -/
#print is_add_group_hom.neg /- _inst_5: add_comm_group ↝ add_group
_inst_6: is_add_group_hom ↝ is_add_hom
 -/
#print ring_hom.is_add_group_hom /- _inst_1: ring ↝ add_group semiring
_inst_2: ring ↝ add_group semiring
 -/
#print is_add_group_hom.sub /- _inst_2: add_comm_group ↝ add_group
 -/
#print additive.is_add_group_hom /- _inst_3: is_group_hom ↝ is_mul_hom
 -/
#print multiplicative.is_group_hom /- _inst_3: is_add_group_hom ↝ is_add_hom
 -/

-- deprecated\ring.lean
#print is_ring_hom.is_add_group_hom /- _inst_3: is_ring_hom ↝ is_add_hom
 -/

-- deprecated\subfield.lean
#print range.is_subfield /- _inst_1: field ↝ is_subfield semiring
 -/
#print field.closure /- _inst_1: field ↝ ring has_div
 -/

-- deprecated\subgroup.lean
#print gpowers /- _inst_1: group ↝ has_pow
 -/
#print normal_add_subgroup_of_add_comm_group /- _inst_1: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print normal_subgroup_of_comm_group /- _inst_1: comm_group ↝ comm_semigroup group
 -/
#print is_subgroup.trivial /- _inst_2: group ↝ has_one
 -/
#print is_add_subgroup.trivial /- _inst_2: add_group ↝ has_zero
 -/
#print is_subgroup.eq_trivial_iff /- _inst_2: is_subgroup ↝ is_submonoid
 -/
#print is_add_subgroup.eq_trivial_iff /- _inst_2: is_add_subgroup ↝ is_add_submonoid
 -/
#print is_subgroup.center /- _inst_2: group ↝ has_mul
 -/
#print is_add_subgroup.add_center /- _inst_2: add_group ↝ has_add
 -/
#print is_subgroup.normalizer /- _inst_1: group ↝ has_inv has_mul
 -/
#print is_add_subgroup.add_normalizer /- _inst_1: add_group ↝ has_neg has_add
 -/
#print is_group_hom.range_subgroup /- _inst_3: is_group_hom ↝ is_subgroup
 -/
#print is_add_group_hom.range_add_subgroup /- _inst_3: is_add_group_hom ↝ is_add_subgroup
 -/
#print is_group_hom.normal_subgroup_ker /- _inst_3: is_group_hom ↝ normal_subgroup
 -/
#print is_add_group_hom.normal_add_subgroup_ker /- _inst_3: is_add_group_hom ↝ normal_add_subgroup
 -/
#print subtype_mk.is_add_group_hom /- _inst_4: is_add_group_hom ↝ is_add_monoid_hom
 -/
#print subtype_mk.is_group_hom /- _inst_4: is_group_hom ↝ is_monoid_hom
 -/
#print group.mem_closure_union_iff /- _inst_2: comm_group ↝ group comm_monoid
 -/
#print add_group.mem_closure_union_iff /- _inst_2: add_comm_group ↝ add_comm_monoid add_group
 -/

-- deprecated\submonoid.lean
#print powers /- _inst_1: monoid ↝ has_pow
 -/
#print multiples /- _inst_2: add_monoid ↝ has_zero has_add
 -/
#print range.is_add_submonoid /- _inst_4: is_add_monoid_hom ↝ is_add_submonoid
 -/
#print range.is_submonoid /- _inst_4: is_monoid_hom ↝ is_submonoid
 -/
#print add_monoid.mem_closure_union_iff /- _inst_3: add_comm_monoid ↝ add_monoid add_comm_semigroup
 -/
#print monoid.mem_closure_union_iff /- _inst_3: comm_monoid ↝ monoid comm_semigroup
 -/

-- deprecated\subring.lean
#print ring_hom.is_subring_preimage /- _inst_4: is_subring ↝ is_add_subgroup is_submonoid
 -/
#print ring_hom.is_subring_image /- _inst_4: is_subring ↝ is_add_subgroup is_submonoid
 -/
#print ring_hom.is_subring_set_range /- _inst_2: ring ↝ is_add_subgroup semiring is_add_group_hom
 -/
#print is_subring.inter /- _inst_3: is_subring ↝ is_add_subgroup is_submonoid
_inst_4: is_subring ↝ is_add_subgroup is_submonoid
 -/
#print ring.closure /- _inst_1: ring ↝ monoid add_group
 -/
#print ring.closure_subset /- _inst_3: is_subring ↝ is_add_subgroup is_submonoid
 -/
#print ring.closure_subset_iff /- _inst_3: is_subring ↝ is_add_subgroup is_submonoid
 -/

-- dynamics\fixed_points\basic.lean
#print function.is_fixed_pt.decidable /- h: decidable_eq ↝
 -/
#print function.fixed_points.decidable /- _inst_1: decidable_eq ↝
 -/

-- dynamics\periodic_pts.lean
#print function.is_periodic_pt.decidable /- _inst_1: decidable_eq ↝
 -/

-- field_theory\algebraic_closure.lean
#print is_alg_closure /- _inst_1: field ↝ comm_ring
 -/
#print algebraic_closure.monic_irreducible /- _inst_1: field ↝ ring
 -/

-- field_theory\chevalley_warning.lean
#print mv_polynomial.sum_mv_polynomial_eq_zero /- _inst_4: decidable_eq ↝
 -/
#print char_dvd_card_solutions_family /- _inst_4: decidable_eq ↝
_inst_5: decidable_eq ↝
 -/
#print char_dvd_card_solutions /- _inst_4: decidable_eq ↝
_inst_5: decidable_eq ↝
 -/

-- field_theory\finite\basic.lean
#print finite_field.card_image_polynomial_eval /- _inst_4: decidable_eq ↝
 -/
#print finite_field.card_units /- _inst_1: field ↝ division_ring
 -/
#print finite_field.prod_univ_units_id_eq_neg_one /- _inst_1: field ↝ integral_domain
 -/
#print finite_field.card /- _inst_1: field ↝ integral_domain
 -/

-- field_theory\finite\polynomial.lean
#print mv_polynomial.indicator /- _inst_1: field ↝ integral_domain
 -/
#print mv_polynomial.evalₗ /- _inst_2: fintype ↝
_inst_3: fintype ↝
 -/
#print mv_polynomial.R /- _inst_1: fintype ↝
 -/

-- field_theory\fixed.lean
#print fixed_by.is_subfield /- _inst_1: group ↝ monoid
 -/
#print fixed_points.mul_action.fixed_points.is_subfield /- _inst_1: group ↝ monoid is_subfield
_inst_3: mul_semiring_action ↝ is_subfield
 -/
#print fixed_points.mul_action.fixed_points.is_invariant_subring /- _inst_1: group ↝ monoid is_subfield
_inst_2: field ↝ ring is_subfield
 -/
#print fixed_points.smul /- _inst_1: group ↝ is_invariant_subring monoid mul_semiring_action is_subfield
_inst_2: field ↝ is_invariant_subring mul_semiring_action ring is_subfield
 -/

-- field_theory\minimal_polynomial.lean
#print minimal_polynomial.degree_pos /- _inst_1: integral_domain ↝ comm_ring
 -/
#print minimal_polynomial.aeval_ne_zero_of_dvd_not_unit_minimal_polynomial /- _inst_2: domain ↝ ring
 -/
#print minimal_polynomial.dvd_map_of_is_scalar_tower /- _inst_10: is_scalar_tower ↝
 -/
#print minimal_polynomial.gcd_domain_eq_field_fractions /- _inst_8: integral_domain ↝ comm_ring domain
_inst_11: is_scalar_tower ↝
 -/
#print minimal_polynomial.prime /- _inst_2: domain ↝ nontrivial ring no_zero_divisors
 -/
#print minimal_polynomial.root /- _inst_1: field ↝ integral_domain
 -/

-- field_theory\mv_polynomial.lean
#print mv_polynomial.restrict_total_degree /- _inst_1: field ↝ comm_ring
 -/
#print mv_polynomial.restrict_degree /- _inst_1: field ↝ comm_ring
 -/
#print mv_polynomial.map_range_eq_map /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/
#print mv_polynomial.is_basis_monomials /- _inst_1: field ↝ comm_ring
 -/

-- field_theory\primitive_element.lean
#print field.primitive_element_inf_aux_exists_c /- _inst_1: field ↝ division_ring
_inst_3: field ↝ integral_domain has_div
 -/

-- field_theory\separable.lean
#print polynomial.separable_X_sub_C /- _inst_1: comm_ring ↝ ring comm_semiring
 -/
#print polynomial.separable.inj_of_prod_X_sub_C /- _inst_1: comm_ring ↝ ring comm_semiring
 -/
#print polynomial.of_irreducible_expand /- _inst_1: field ↝ integral_domain
 -/
#print polynomial.expand_char /- _inst_1: field ↝ comm_ring
 -/
#print polynomial.is_unit_or_eq_zero_of_separable_expand /- _inst_1: field ↝ integral_domain
 -/
#print polynomial.not_unit_X_sub_C /- _inst_1: field ↝ integral_domain
 -/
#print polynomial.multiplicity_le_one_of_separable /- _inst_1: field ↝ comm_ring
 -/
#print is_separable /- _inst_1: field ↝ comm_ring
_inst_2: field ↝ ring
 -/
#print is_separable_tower_top_of_is_separable /- _inst_7: is_scalar_tower ↝
 -/
#print is_separable_tower_bot_of_is_separable /- _inst_7: is_scalar_tower ↝
 -/

-- field_theory\splitting_field.lean
#print polynomial.splits /- _inst_1: field ↝ semiring
_inst_2: field ↝ ring
 -/
#print polynomial.roots_map /- _inst_2: field ↝ integral_domain
 -/
#print lift_of_splits /- _inst_3: field ↝ integral_domain
 -/
#print polynomial.factor /- _inst_1: field ↝ ring
 -/
#print polynomial.is_splitting_field.map /- _inst_7: is_scalar_tower ↝
 -/
#print polynomial.is_splitting_field.mul /- _inst_7: is_scalar_tower ↝
 -/

-- field_theory\subfield.lean
#print ring_hom.mem_field_range /- _inst_1: field ↝ ring
_inst_2: field ↝ ring
 -/
#print ring_hom.restrict_field /- _inst_2: field ↝ semiring
 -/
#print ring_hom.eq_of_eq_on_subfield_top /- _inst_2: field ↝ semiring
 -/

-- field_theory\tower.lean
#print dim_mul_dim' /- _inst_7: is_scalar_tower ↝
 -/
#print dim_mul_dim /- _inst_14: is_scalar_tower ↝
 -/
#print finite_dimensional.trans /- _inst_7: is_scalar_tower ↝
 -/
#print finite_dimensional.right /- _inst_7: is_scalar_tower ↝
 -/
#print finite_dimensional.findim_mul_findim /- _inst_7: is_scalar_tower ↝
 -/
#print finite_dimensional.linear_map /- _inst_10: vector_space ↝
_inst_12: vector_space ↝
 -/
#print finite_dimensional.findim_linear_map /- _inst_10: vector_space ↝ finite_dimensional
_inst_12: vector_space ↝ finite_dimensional
 -/
#print finite_dimensional.linear_map' /- _inst_13: vector_space ↝ finite_dimensional
 -/
#print finite_dimensional.findim_linear_map' /- _inst_13: vector_space ↝
 -/

-- geometry\euclidean\basic.lean
#print euclidean_geometry.cospherical /- _inst_2: metric_space ↝ has_dist
 -/

-- geometry\manifold\algebra\lie_group.lean
#print lie_add_group.to_has_smooth_add /- _inst_4: normed_space ↝
 -/
#print lie_group.to_has_smooth_mul /- _inst_4: normed_space ↝
 -/
#print smooth_pow /- _inst_4: normed_space ↝
 -/
#print smooth_neg /- _inst_4: normed_space ↝
 -/
#print smooth_inv /- _inst_4: normed_space ↝
 -/
#print smooth.neg /- _inst_4: normed_space ↝ smooth_manifold_with_corners
_inst_13: normed_space ↝
 -/
#print smooth.inv /- _inst_4: normed_space ↝ smooth_manifold_with_corners
_inst_13: normed_space ↝
 -/
#print smooth_on.inv /- _inst_4: normed_space ↝ smooth_manifold_with_corners
_inst_13: normed_space ↝
 -/
#print smooth_on.neg /- _inst_4: normed_space ↝ smooth_manifold_with_corners
_inst_13: normed_space ↝
 -/
#print prod.lie_group /- _inst_4: normed_space ↝ smooth_manifold_with_corners has_smooth_mul
_inst_11: normed_space ↝ smooth_manifold_with_corners has_smooth_mul
 -/
#print prod.lie_add_group /- _inst_4: normed_space ↝ smooth_manifold_with_corners has_smooth_add
_inst_11: normed_space ↝ smooth_manifold_with_corners has_smooth_add
 -/
#print lie_add_group_morphism.has_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print lie_group_morphism.has_one /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print lie_add_group_morphism.inhabited /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print lie_group_morphism.inhabited /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print lie_group_morphism.has_coe_to_fun /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print lie_add_group_morphism.has_coe_to_fun /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print lie_add_group_core.to_smooth_manifold_with_corners /- _inst_3: normed_space ↝
 -/
#print lie_group_core.to_smooth_manifold_with_corners /- _inst_3: normed_space ↝
 -/
#print lie_group_core.to_topological_group /- _inst_3: normed_space ↝
 -/
#print lie_add_group_core.to_topological_add_group /- _inst_3: normed_space ↝
 -/
#print lie_add_group_core.to_lie_add_group /- _inst_3: normed_space ↝
 -/
#print lie_group_core.to_lie_group /- _inst_3: normed_space ↝
 -/
#print normed_space_lie_group /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/

-- geometry\manifold\algebra\monoid.lean
#print has_smooth_add.to_smooth_manifold_with_corners /- _inst_5: normed_space ↝
 -/
#print has_smooth_mul.to_smooth_manifold_with_corners /- _inst_5: normed_space ↝
 -/
#print smooth_mul /- _inst_5: normed_space ↝
 -/
#print smooth_add /- _inst_5: normed_space ↝
 -/
#print smooth.add /- _inst_5: normed_space ↝ smooth_manifold_with_corners
_inst_12: normed_space ↝
 -/
#print smooth.mul /- _inst_5: normed_space ↝ smooth_manifold_with_corners
_inst_12: normed_space ↝
 -/
#print smooth_add_left /- _inst_5: normed_space ↝ smooth_manifold_with_corners
 -/
#print smooth_mul_left /- _inst_5: normed_space ↝ smooth_manifold_with_corners
 -/
#print smooth_add_right /- _inst_5: normed_space ↝ smooth_manifold_with_corners
 -/
#print smooth_mul_right /- _inst_5: normed_space ↝ smooth_manifold_with_corners
 -/
#print smooth_on.add /- _inst_5: normed_space ↝ smooth_manifold_with_corners
_inst_12: normed_space ↝
 -/
#print smooth_on.mul /- _inst_5: normed_space ↝ smooth_manifold_with_corners
_inst_12: normed_space ↝
 -/
#print has_smooth_mul.prod /- _inst_19: normed_space ↝ smooth_manifold_with_corners
_inst_27: normed_space ↝ smooth_manifold_with_corners
 -/
#print has_smooth_add.sum /- _inst_19: normed_space ↝ smooth_manifold_with_corners
_inst_27: normed_space ↝ smooth_manifold_with_corners
 -/
#print smooth_monoid_morphism.has_one /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print smooth_add_monoid_morphism.has_zero /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print smooth_monoid_morphism.inhabited /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print smooth_add_monoid_morphism.inhabited /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print smooth_monoid_morphism.has_coe_to_fun /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print smooth_add_monoid_morphism.has_coe_to_fun /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print has_smooth_add_core.to_has_continuous_add /- _inst_4: normed_space ↝
_inst_9: add_group ↝ has_add
 -/
#print has_smooth_mul_core.to_has_continuous_mul /- _inst_4: normed_space ↝
_inst_9: group ↝ has_mul
 -/
#print has_smooth_add_core.to_has_smooth_add /- _inst_4: normed_space ↝
 -/
#print has_smooth_mul_core.to_has_smooth_mul /- _inst_4: normed_space ↝
 -/

-- geometry\manifold\algebra\smooth_functions.lean
#print smooth_map.has_mul /- _inst_3: normed_space ↝
_inst_5: normed_space ↝ smooth_manifold_with_corners
 -/
#print smooth_map.has_add /- _inst_3: normed_space ↝
_inst_5: normed_space ↝ smooth_manifold_with_corners
 -/
#print smooth_map.has_zero /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_11: add_monoid ↝ has_zero
 -/
#print smooth_map.has_one /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_11: monoid ↝ has_one
 -/
#print smooth_map_semigroup /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print smooth_map_add_semigroup /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print smooth_map_add_monoid /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print smooth_map_monoid /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print smooth_map_add_comm_monoid /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print smooth_map_comm_monoid /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print smooth_map_add_group /- _inst_3: normed_space ↝
_inst_5: normed_space ↝ has_smooth_add
 -/
#print smooth_map_group /- _inst_3: normed_space ↝
_inst_5: normed_space ↝ has_smooth_mul
 -/
#print smooth_map_comm_group /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print smooth_map_add_comm_group /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print smooth_map_semiring /- _inst_3: normed_space ↝
_inst_5: normed_space ↝ has_smooth_mul has_smooth_add
 -/
#print smooth_map_ring /- _inst_3: normed_space ↝
_inst_5: normed_space ↝ smooth_semiring
 -/
#print smooth_map_comm_ring /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print smooth_map_has_scalar /- _inst_3: normed_space ↝
_inst_12: normed_space ↝
 -/
#print smooth_map_semimodule /- _inst_3: normed_space ↝
_inst_12: normed_space ↝
 -/
#print smooth_map.C /- _inst_3: normed_space ↝
 -/
#print times_cont_mdiff_map.algebra /- _inst_3: normed_space ↝
 -/
#print smooth_map_has_scalar' /- _inst_3: normed_space ↝
_inst_12: normed_space ↝
 -/
#print smooth_map_module' /- _inst_3: normed_space ↝
_inst_12: normed_space ↝
 -/

-- geometry\manifold\algebra\structures.lean
#print smooth_semiring.to_has_smooth_add /- _inst_4: normed_space ↝
 -/
#print smooth_semiring.to_has_smooth_mul /- _inst_4: normed_space ↝
 -/
#print smooth_ring.to_lie_add_group /- _inst_4: normed_space ↝
 -/
#print smooth_ring.to_has_smooth_mul /- _inst_4: normed_space ↝
 -/
#print smooth_ring.to_smooth_semiring /- _inst_4: normed_space ↝
 -/

-- geometry\manifold\basic_smooth_bundle.lean
#print trivial_basic_smooth_bundle_core /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.inhabited /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.to_topological_fiber_bundle_core /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.base_set /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.chart /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.chart_source /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.chart_target /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.to_charted_space /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.mem_atlas_iff /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.mem_chart_source_iff /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.mem_chart_target_iff /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.coe_chart_at_fst /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.coe_chart_at_symm_fst /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print basic_smooth_bundle_core.to_smooth_manifold /- _inst_3: normed_space ↝ has_groupoid
_inst_9: normed_space ↝
 -/
#print tangent_bundle_core /- _inst_3: normed_space ↝
 -/
#print tangent_space /- _inst_3: normed_space ↝
_inst_7: smooth_manifold_with_corners ↝
 -/
#print tangent_bundle /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.proj /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.proj_apply /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.topological_space /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.charted_space /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.smooth_manifold_with_corners /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print tangent_space.topological_module /- _inst_3: normed_space ↝
 -/
#print tangent_space.topological_space /- _inst_3: normed_space ↝
 -/
#print tangent_space.add_comm_group /- _inst_3: normed_space ↝
 -/
#print tangent_space.topological_add_group /- _inst_3: normed_space ↝
 -/
#print tangent_space.vector_space /- _inst_3: normed_space ↝
 -/
#print tangent_space.inhabited /- _inst_3: normed_space ↝
 -/
#print tangent_bundle_proj_continuous /- _inst_3: normed_space ↝
 -/
#print tangent_bundle_proj_open /- _inst_3: normed_space ↝
 -/
#print tangent_bundle_model_space_chart_at /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print tangent_bundle_model_space_coe_chart_at /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print tangent_bundle_model_space_coe_chart_at_symm /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print tangent_bundle_model_space_homeomorph /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print tangent_bundle_model_space_homeomorph_coe /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print tangent_bundle_model_space_homeomorph_coe_symm /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/

-- geometry\manifold\diffeomorph.lean
#print diffeomorph /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_diffeomorph.has_coe_to_fun /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_diffeomorph.times_cont_mdiff_map.has_coe /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_diffeomorph.continuous /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_diffeomorph.times_cont_mdiff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_diffeomorph.smooth /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_diffeomorph.coe_eq_to_equiv /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_diffeomorph.refl /- _inst_3: normed_space ↝
 -/
#print times_diffeomorph.trans /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_diffeomorph.symm /- _inst_3: normed_space ↝
_inst_7: normed_space ↝
 -/

-- geometry\manifold\mfderiv.lean
#print unique_mdiff_within_at /- _inst_3: normed_space ↝
 -/
#print unique_mdiff_on /- _inst_3: normed_space ↝
 -/
#print written_in_ext_chart_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mfderiv_within /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mfderiv /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map_within /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print unique_mdiff_within_at_univ /- _inst_3: normed_space ↝
 -/
#print unique_mdiff_within_at_iff /- _inst_3: normed_space ↝
 -/
#print unique_mdiff_within_at.mono /- _inst_3: normed_space ↝
 -/
#print unique_mdiff_within_at.inter' /- _inst_3: normed_space ↝
 -/
#print unique_mdiff_within_at.inter /- _inst_3: normed_space ↝
 -/
#print is_open.unique_mdiff_within_at /- _inst_3: normed_space ↝
 -/
#print unique_mdiff_on.inter /- _inst_3: normed_space ↝
 -/
#print is_open.unique_mdiff_on /- _inst_3: normed_space ↝
 -/
#print unique_mdiff_on_univ /- _inst_3: normed_space ↝
 -/
#print unique_mdiff_within_at.eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print unique_mdiff_on.eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at_iff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mfderiv_within_zero_of_not_mdifferentiable_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mfderiv_zero_of_not_mdifferentiable_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at.mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_at.has_mfderiv_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at.mdifferentiable_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_at.mdifferentiable_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_at_unique /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at_inter' /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at_inter /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at.union /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at.nhds_within /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at.has_mfderiv_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at.has_mfderiv_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at.mfderiv_within /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_at.has_mfderiv_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_at.mfderiv /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_at.mfderiv /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at.mfderiv_within /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable.mfderiv_within /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mfderiv_within_subset /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at.mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at_inter /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at_inter' /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_at.mdifferentiable_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at.mdifferentiable_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_on.mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_on_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable.mdifferentiable_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_on_of_locally_mdifferentiable_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mfderiv_within_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mfderiv_within_inter /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at.continuous_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_at.continuous_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at.continuous_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_at.continuous_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_on.continuous_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable.continuous /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map_within_subset /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map_within_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map_within_eq_tangent_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map_within_tangent_bundle_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map_within_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map_tangent_bundle_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_within_at.congr_mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print has_mfderiv_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print filter.eventually_eq.mdifferentiable_within_at_iff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at.congr_mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at.congr /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_on.congr_mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mdifferentiable_within_at.mfderiv_within_congr_mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print filter.eventually_eq.mfderiv_within_eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print mfderiv_within_congr /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_map_within_congr /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print filter.eventually_eq.mfderiv_eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print written_in_ext_chart_comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print has_mfderiv_within_at.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print has_mfderiv_at.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print has_mfderiv_at.comp_has_mfderiv_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print mdifferentiable_within_at.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print mdifferentiable_at.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print mfderiv_within_comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print mfderiv_comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print mdifferentiable_on.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print mdifferentiable.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print tangent_map_within_comp_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print tangent_map_comp_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print tangent_map_comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print has_mfderiv_at_id /- _inst_3: normed_space ↝
 -/
#print has_mfderiv_within_at_id /- _inst_3: normed_space ↝
 -/
#print mdifferentiable_at_id /- _inst_3: normed_space ↝
 -/
#print mdifferentiable_within_at_id /- _inst_3: normed_space ↝
 -/
#print mdifferentiable_id /- _inst_3: normed_space ↝
 -/
#print mdifferentiable_on_id /- _inst_3: normed_space ↝
 -/
#print mfderiv_id /- _inst_3: normed_space ↝
 -/
#print mfderiv_within_id /- _inst_3: normed_space ↝
 -/
#print tangent_map_id /- _inst_3: normed_space ↝
 -/
#print tangent_map_within_id /- _inst_3: normed_space ↝
 -/
#print has_mfderiv_at_const /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print has_mfderiv_within_at_const /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print mdifferentiable_at_const /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print mdifferentiable_within_at_const /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print mdifferentiable_const /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print mdifferentiable_on_const /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print mfderiv_const /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print mfderiv_within_const /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print model_with_corners.mdifferentiable /- _inst_3: normed_space ↝
 -/
#print model_with_corners.mdifferentiable_on_symm /- _inst_3: normed_space ↝
 -/
#print mdifferentiable_at_atlas /- _inst_3: normed_space ↝ has_groupoid
_inst_7: smooth_manifold_with_corners ↝ has_groupoid
 -/
#print mdifferentiable_on_atlas /- _inst_3: normed_space ↝
 -/
#print mdifferentiable_at_atlas_symm /- _inst_3: normed_space ↝ has_groupoid
_inst_7: smooth_manifold_with_corners ↝ has_groupoid
 -/
#print mdifferentiable_on_atlas_symm /- _inst_3: normed_space ↝
 -/
#print mdifferentiable_of_mem_atlas /- _inst_3: normed_space ↝
 -/
#print mdifferentiable_chart /- _inst_3: normed_space ↝
 -/
#print tangent_map_chart /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print tangent_map_chart_symm /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print unique_mdiff_within_at_iff_unique_diff_within_at /- _inst_3: normed_space ↝
 -/
#print unique_mdiff_on_iff_unique_diff_on /- _inst_3: normed_space ↝
 -/
#print written_in_ext_chart_model_space /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print mdifferentiable_within_at_iff_differentiable_within_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print mdifferentiable_at_iff_differentiable_at /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print mdifferentiable_on_iff_differentiable_on /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print mdifferentiable_iff_differentiable /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print mfderiv_within_eq_fderiv_within /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_5: normed_space ↝ smooth_manifold_with_corners
 -/
#print mfderiv_eq_fderiv /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_5: normed_space ↝ smooth_manifold_with_corners
 -/
#print local_homeomorph.mdifferentiable.symm /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable.mdifferentiable_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable.mdifferentiable_at_symm /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable.symm_comp_deriv /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable.comp_symm_deriv /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable.mfderiv /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable.mfderiv_bijective /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable.mfderiv_surjective /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable.range_mfderiv_eq_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print local_homeomorph.mdifferentiable.trans /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
 -/
#print unique_mdiff_on.unique_mdiff_on_preimage /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_9: normed_space ↝ smooth_manifold_with_corners
 -/
#print unique_mdiff_on.unique_diff_on /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print unique_mdiff_on.unique_diff_on_inter_preimage /- _inst_3: normed_space ↝
_inst_9: normed_space ↝
 -/
#print unique_mdiff_on.smooth_bundle_preimage /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_14: normed_space ↝ smooth_manifold_with_corners
 -/
#print unique_mdiff_on.tangent_bundle_proj_preimage /- _inst_3: normed_space ↝
 -/

-- geometry\manifold\smooth_manifold_with_corners.lean
#print model_with_corners_self /- _inst_3: normed_space ↝
 -/
#print model_with_corners.has_coe_to_fun /- _inst_3: normed_space ↝
 -/
#print model_with_corners.symm /- _inst_3: normed_space ↝
 -/
#print model_with_corners.to_local_equiv_coe /- _inst_3: normed_space ↝
 -/
#print model_with_corners.mk_coe /- _inst_3: normed_space ↝
 -/
#print model_with_corners.to_local_equiv_coe_symm /- _inst_3: normed_space ↝
 -/
#print model_with_corners.mk_coe_symm /- _inst_3: normed_space ↝
 -/
#print model_with_corners.unique_diff /- _inst_3: normed_space ↝
 -/
#print model_with_corners.continuous /- _inst_3: normed_space ↝
 -/
#print model_with_corners.continuous_symm /- _inst_3: normed_space ↝
 -/
#print model_with_corners_self_local_equiv /- _inst_3: normed_space ↝
 -/
#print model_with_corners_self_coe /- _inst_3: normed_space ↝
 -/
#print model_with_corners_self_coe_symm /- _inst_3: normed_space ↝
 -/
#print model_with_corners.target /- _inst_3: normed_space ↝
 -/
#print model_with_corners.left_inv /- _inst_3: normed_space ↝
 -/
#print model_with_corners.left_inv' /- _inst_3: normed_space ↝
 -/
#print model_with_corners.right_inv /- _inst_3: normed_space ↝
 -/
#print model_with_corners.image /- _inst_3: normed_space ↝
 -/
#print model_with_corners.unique_diff_preimage /- _inst_3: normed_space ↝
 -/
#print model_with_corners.unique_diff_preimage_source /- _inst_3: normed_space ↝
 -/
#print model_with_corners.unique_diff_at_image /- _inst_3: normed_space ↝
 -/
#print model_with_corners.prod /- _inst_3: normed_space ↝
_inst_6: normed_space ↝
 -/
#print model_with_corners.tangent /- _inst_3: normed_space ↝
 -/
#print model_with_corners_prod_to_local_equiv /- _inst_3: normed_space ↝
_inst_7: normed_space ↝
 -/
#print model_with_corners_prod_coe /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print model_with_corners_prod_coe_symm /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print model_with_corners_self_boundaryless /- _inst_3: normed_space ↝
 -/
#print model_with_corners.range_eq_univ_prod /- _inst_3: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_groupoid /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_groupoid_le /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_groupoid_zero_eq /- _inst_3: normed_space ↝
 -/
#print of_set_mem_times_cont_diff_groupoid /- _inst_3: normed_space ↝
 -/
#print symm_trans_mem_times_cont_diff_groupoid /- _inst_3: normed_space ↝
 -/
#print times_cont_diff_groupoid_prod /- _inst_3: normed_space ↝
_inst_7: normed_space ↝
 -/
#print times_cont_diff_groupoid.closed_under_restriction /- _inst_3: normed_space ↝
 -/
#print smooth_manifold_with_corners.to_has_groupoid /- _inst_3: normed_space ↝
 -/
#print smooth_manifold_with_corners_of_times_cont_diff_on /- _inst_3: normed_space ↝
 -/
#print model_space_smooth /- _inst_3: normed_space ↝
 -/
#print smooth_manifold_with_corners.maximal_atlas /- _inst_3: normed_space ↝
 -/
#print smooth_manifold_with_corners.mem_maximal_atlas_of_mem_atlas /- _inst_3: normed_space ↝ has_groupoid
_inst_7: smooth_manifold_with_corners ↝ has_groupoid
 -/
#print smooth_manifold_with_corners.chart_mem_maximal_atlas /- _inst_3: normed_space ↝ has_groupoid
_inst_7: smooth_manifold_with_corners ↝ has_groupoid
 -/
#print smooth_manifold_with_corners.compatible_of_mem_maximal_atlas /- _inst_3: normed_space ↝
 -/
#print smooth_manifold_with_corners.prod /- _inst_9: normed_space ↝ has_groupoid
_inst_11: normed_space ↝ has_groupoid
_inst_16: smooth_manifold_with_corners ↝ has_groupoid
_inst_19: smooth_manifold_with_corners ↝ has_groupoid
 -/
#print ext_chart_at /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_source /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_open_source /- _inst_3: normed_space ↝
 -/
#print mem_ext_chart_source /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_to_inv /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_source_mem_nhds /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_continuous_on /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_continuous_at /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_continuous_on_symm /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_target_mem_nhds_within /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_coe /- _inst_3: normed_space ↝
 -/
#print ext_chart_at_coe_symm /- _inst_3: normed_space ↝
 -/
#print nhds_within_ext_chart_target_eq /- _inst_3: normed_space ↝
 -/
#print ext_chart_continuous_at_symm' /- _inst_3: normed_space ↝
 -/
#print ext_chart_continuous_at_symm /- _inst_3: normed_space ↝
 -/
#print ext_chart_preimage_mem_nhds_within' /- _inst_3: normed_space ↝
 -/
#print ext_chart_preimage_mem_nhds_within /- _inst_3: normed_space ↝
 -/
#print ext_chart_preimage_mem_nhds /- _inst_3: normed_space ↝
 -/
#print ext_chart_preimage_inter_eq /- _inst_3: normed_space ↝
 -/
#print ext_chart_model_space_eq_id /- _inst_3: normed_space ↝
 -/

-- geometry\manifold\times_cont_mdiff.lean
#print times_cont_diff_within_at_prop /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_diff_within_at_local_invariant_prop /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_diff_within_at_local_invariant_prop_mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_diff_within_at_local_invariant_prop_id /- _inst_3: normed_space ↝
 -/
#print times_cont_mdiff_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff.smooth /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth.times_cont_mdiff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on.smooth_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_on.times_cont_mdiff_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at.smooth_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_at.times_cont_mdiff_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at.smooth_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_within_at.times_cont_mdiff_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff.times_cont_mdiff_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth.smooth_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_at_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_on_univ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_iff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_within_at_iff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on_iff /- _inst_3: normed_space ↝ has_groupoid
Is: smooth_manifold_with_corners ↝ has_groupoid
_inst_8: normed_space ↝ has_groupoid
I's: smooth_manifold_with_corners ↝ has_groupoid
 -/
#print smooth_on_iff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_iff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_iff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at.of_le /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at.of_le /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on.of_le /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff.of_le /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at.of_succ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at.of_succ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on.of_succ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff.of_succ /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at.continuous_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at.continuous_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on.continuous_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff.continuous /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at.mdifferentiable_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at.mdifferentiable_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on.mdifferentiable_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff.mdifferentiable /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth.mdifferentiable /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth.mdifferentiable_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth.mdifferentiable_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_top /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at_top /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on_top /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_top /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_iff_nat /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at.mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at.times_cont_mdiff_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_at.smooth_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on.mono /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff.times_cont_mdiff_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth.smooth_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_inter' /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_inter /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at.times_cont_mdiff_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_within_at.smooth_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds /- _inst_3: normed_space ↝ has_groupoid
Is: smooth_manifold_with_corners ↝ has_groupoid
_inst_8: normed_space ↝ has_groupoid
I's: smooth_manifold_with_corners ↝ has_groupoid
 -/
#print times_cont_mdiff_at_iff_times_cont_mdiff_on_nhds /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at.congr /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_congr /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print filter.eventually_eq.times_cont_mdiff_within_at_iff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at.congr_of_eventually_eq /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print filter.eventually_eq.times_cont_mdiff_at_iff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on.congr /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on_congr /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on_of_locally_times_cont_mdiff_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_of_locally_times_cont_mdiff_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_23: normed_space ↝
 -/
#print times_cont_mdiff_on.comp' /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_23: normed_space ↝
 -/
#print times_cont_mdiff.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_23: normed_space ↝
 -/
#print times_cont_mdiff_within_at.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_23: normed_space ↝
 -/
#print times_cont_mdiff_within_at.comp' /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_23: normed_space ↝
 -/
#print times_cont_mdiff_at.comp /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_23: normed_space ↝
 -/
#print times_cont_mdiff.comp_times_cont_mdiff_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_23: normed_space ↝
 -/
#print smooth.comp_smooth_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_23: normed_space ↝
 -/
#print times_cont_mdiff_on_of_mem_maximal_atlas /- _inst_3: normed_space ↝ has_groupoid
Is: smooth_manifold_with_corners ↝ has_groupoid
 -/
#print times_cont_mdiff_on_symm_of_mem_maximal_atlas /- _inst_3: normed_space ↝ has_groupoid
Is: smooth_manifold_with_corners ↝ has_groupoid
 -/
#print times_cont_mdiff_on_chart /- _inst_3: normed_space ↝ has_groupoid
 -/
#print times_cont_mdiff_on_chart_symm /- _inst_3: normed_space ↝ has_groupoid
 -/
#print times_cont_mdiff_id /- _inst_3: normed_space ↝
 -/
#print smooth_id /- _inst_3: normed_space ↝
 -/
#print times_cont_mdiff_on_id /- _inst_3: normed_space ↝
 -/
#print smooth_on_id /- _inst_3: normed_space ↝
 -/
#print times_cont_mdiff_at_id /- _inst_3: normed_space ↝
 -/
#print smooth_at_id /- _inst_3: normed_space ↝
 -/
#print times_cont_mdiff_within_at_id /- _inst_3: normed_space ↝
 -/
#print smooth_within_at_id /- _inst_3: normed_space ↝
 -/
#print times_cont_mdiff_const /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_const /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on_const /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_on_const /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at_const /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_at_const /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_const /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print smooth_within_at_const /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_within_at_iff_times_cont_diff_within_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_at_iff_times_cont_diff_at /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on_iff_times_cont_diff_on /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_iff_times_cont_diff /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff_on.continuous_on_tangent_map_within_aux /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_8: normed_space ↝ smooth_manifold_with_corners
 -/
#print times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within_aux /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_8: normed_space ↝ smooth_manifold_with_corners
 -/
#print times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_8: normed_space ↝ smooth_manifold_with_corners
 -/
#print times_cont_mdiff_on.continuous_on_tangent_map_within /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff.times_cont_mdiff_tangent_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print times_cont_mdiff.continuous_tangent_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print basic_smooth_bundle_core.times_cont_mdiff_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print basic_smooth_bundle_core.smooth_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print basic_smooth_bundle_core.times_cont_mdiff_on_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print basic_smooth_bundle_core.smooth_on_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print basic_smooth_bundle_core.times_cont_mdiff_at_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print basic_smooth_bundle_core.smooth_at_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print basic_smooth_bundle_core.times_cont_mdiff_within_at_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print basic_smooth_bundle_core.smooth_within_at_proj /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print basic_smooth_bundle_core.smooth_const_section /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
 -/
#print tangent_bundle.times_cont_mdiff_proj /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.smooth_proj /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.times_cont_mdiff_on_proj /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.smooth_on_proj /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.times_cont_mdiff_at_proj /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.smooth_at_proj /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.times_cont_mdiff_within_at_proj /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.smooth_within_at_proj /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.zero_section /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.smooth_zero_section /- _inst_3: normed_space ↝
 -/
#print tangent_bundle.tangent_map_tangent_bundle_pure /- _inst_3: normed_space ↝ smooth_manifold_with_corners
 -/
#print times_cont_mdiff_within_at.prod_mk /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_18: normed_space ↝
 -/
#print times_cont_mdiff_at.prod_mk /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_18: normed_space ↝
 -/
#print times_cont_mdiff_on.prod_mk /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_18: normed_space ↝
 -/
#print times_cont_mdiff.prod_mk /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_18: normed_space ↝
 -/
#print smooth_within_at.prod_mk /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_18: normed_space ↝
 -/
#print smooth_at.prod_mk /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_18: normed_space ↝
 -/
#print smooth_on.prod_mk /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_18: normed_space ↝
 -/
#print smooth.prod_mk /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_18: normed_space ↝
 -/
#print times_cont_mdiff_within_at_fst /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_mdiff_at_fst /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_mdiff_on_fst /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_mdiff_fst /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print smooth_within_at_fst /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print smooth_at_fst /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print smooth_on_fst /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print smooth_fst /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_mdiff_within_at_snd /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_mdiff_at_snd /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_mdiff_on_snd /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print times_cont_mdiff_snd /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print smooth_within_at_snd /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print smooth_at_snd /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print smooth_on_snd /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print smooth_snd /- _inst_3: normed_space ↝
_inst_13: normed_space ↝
 -/
#print smooth_iff_proj_smooth /- _inst_3: normed_space ↝
_inst_8: normed_space ↝ smooth_manifold_with_corners
_inst_18: normed_space ↝ smooth_manifold_with_corners
 -/
#print times_cont_mdiff_within_at.prod_map' /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_8: normed_space ↝
_inst_13: normed_space ↝ smooth_manifold_with_corners
_inst_18: normed_space ↝
 -/
#print times_cont_mdiff_within_at.prod_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
_inst_18: normed_space ↝
 -/
#print times_cont_mdiff_at.prod_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
_inst_18: normed_space ↝
 -/
#print times_cont_mdiff_at.prod_map' /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
_inst_18: normed_space ↝
 -/
#print times_cont_mdiff_on.prod_map /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_8: normed_space ↝
_inst_13: normed_space ↝ smooth_manifold_with_corners
_inst_18: normed_space ↝
 -/
#print times_cont_mdiff.prod_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
_inst_18: normed_space ↝
 -/
#print smooth_within_at.prod_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
_inst_18: normed_space ↝
 -/
#print smooth_at.prod_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
_inst_18: normed_space ↝
 -/
#print smooth_on.prod_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
_inst_18: normed_space ↝
 -/
#print smooth.prod_map /- _inst_3: normed_space ↝
_inst_8: normed_space ↝
_inst_13: normed_space ↝
_inst_18: normed_space ↝
 -/
#print continuous_linear_map.times_cont_mdiff /- _inst_3: normed_space ↝ smooth_manifold_with_corners
_inst_13: normed_space ↝ smooth_manifold_with_corners
 -/
#print smooth_smul /- _inst_23: normed_space ↝ smooth_manifold_with_corners
 -/
#print smooth.smul /- _inst_3: normed_space ↝
_inst_23: normed_space ↝ smooth_manifold_with_corners
 -/

-- geometry\manifold\times_cont_mdiff_map.lean
#print smooth_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_mdiff_map.has_coe_to_fun /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_mdiff_map.continuous_map.has_coe /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_mdiff_map.times_cont_mdiff /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_mdiff_map.smooth /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_mdiff_map.coe_inj /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_mdiff_map.ext /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_mdiff_map.id /- _inst_3: normed_space ↝
 -/
#print times_cont_mdiff_map.comp /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_15: normed_space ↝
 -/
#print times_cont_mdiff_map.comp_apply /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
_inst_15: normed_space ↝
 -/
#print times_cont_mdiff_map.inhabited /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print times_cont_mdiff_map.const /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/
#print continuous_linear_map.has_coe_to_times_cont_mdiff_map /- _inst_3: normed_space ↝
_inst_5: normed_space ↝
 -/

-- group_theory\abelianization.lean
#print abelianization.commutator_subset_ker /- _inst_2: comm_group ↝ comm_semigroup group
 -/

-- group_theory\congruence.lean
#print con.quotient.inhabited /- _inst_1: monoid ↝ has_one has_coe_t has_mul
 -/
#print add_con.quotient.inhabited /- _inst_1: add_monoid ↝ has_coe_t has_zero has_add
 -/

-- group_theory\free_group.lean
#print free_group.to_group.aux /- _inst_1: group ↝ has_inv has_one has_mul
 -/
#print free_group.reduce /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.cons /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.red /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.not /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.min /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.idem /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.step.eq /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.eq_of_red /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.sound /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.exact /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.self /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.rev /- _inst_1: decidable_eq ↝
 -/
#print free_group.to_word /- _inst_1: decidable_eq ↝
 -/
#print free_group.to_word.mk /- _inst_1: decidable_eq ↝
 -/
#print free_group.to_word.inj /- _inst_1: decidable_eq ↝
 -/
#print free_group.reduce.church_rosser /- _inst_1: decidable_eq ↝
 -/
#print free_group.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print free_group.red.decidable_rel /- _inst_1: decidable_eq ↝
 -/
#print free_group.red.enum /- _inst_1: decidable_eq ↝
 -/
#print free_group.red.enum.sound /- _inst_1: decidable_eq ↝
 -/
#print free_group.red.enum.complete /- _inst_1: decidable_eq ↝
 -/
#print free_group.subtype.fintype /- _inst_1: decidable_eq ↝
 -/

-- group_theory\group_action\basic.lean
#print mul_action.orbit /- _inst_2: mul_action ↝ has_scalar
 -/
#print mul_action.mem_orbit_iff /- _inst_2: mul_action ↝
 -/
#print mul_action.mem_orbit /- _inst_2: mul_action ↝
 -/
#print mul_action.mem_orbit_self /- _inst_2: mul_action ↝
 -/
#print mul_action.stabilizer_carrier /- _inst_2: mul_action ↝ has_scalar
 -/
#print mul_action.mem_stabilizer_iff /- _inst_2: mul_action ↝
 -/
#print mul_action.fixed_points /- _inst_2: mul_action ↝ has_scalar
 -/
#print mul_action.fixed_by /- _inst_2: mul_action ↝ has_scalar
 -/
#print mul_action.fixed_eq_Inter_fixed_by /- _inst_2: mul_action ↝
 -/
#print mul_action.mem_fixed_points /- _inst_2: mul_action ↝
 -/
#print mul_action.mem_fixed_by /- _inst_2: mul_action ↝
 -/
#print mul_action.mem_fixed_points' /- _inst_2: mul_action ↝
 -/
#print mul_action.stabilizer.submonoid /- _inst_2: mul_action ↝
 -/
#print mul_action.stabilizer /- _inst_2: mul_action ↝
 -/
#print mul_action.orbit_eq_iff /- _inst_2: mul_action ↝
 -/
#print mul_action.stabilizer.subgroup /- _inst_2: mul_action ↝
 -/
#print mul_action.mem_orbit_smul /- _inst_2: mul_action ↝
 -/
#print mul_action.smul_mem_orbit_smul /- _inst_2: mul_action ↝
 -/
#print mul_action.orbit_rel /- _inst_2: mul_action ↝
 -/
#print mul_action.of_quotient_stabilizer /- _inst_2: mul_action ↝
 -/
#print mul_action.of_quotient_stabilizer_mk /- _inst_2: mul_action ↝
 -/
#print mul_action.of_quotient_stabilizer_mem_orbit /- _inst_2: mul_action ↝
 -/
#print mul_action.of_quotient_stabilizer_smul /- _inst_2: mul_action ↝
 -/
#print mul_action.injective_of_quotient_stabilizer /- _inst_2: mul_action ↝
 -/
#print mul_action.orbit_equiv_quotient_stabilizer /- _inst_2: mul_action ↝
 -/
#print mul_action.orbit_equiv_quotient_stabilizer_symm_apply /- _inst_2: mul_action ↝
 -/
#print list.smul_sum /- _inst_3: distrib_mul_action ↝
 -/
#print multiset.smul_sum /- _inst_3: distrib_mul_action ↝
 -/
#print finset.smul_sum /- _inst_3: distrib_mul_action ↝
 -/

-- group_theory\group_action\defs.lean
#print smul_comm_class.symm /- _inst_3: smul_comm_class ↝
 -/
#print smul_comm_class_self /- _inst_1: comm_monoid ↝ monoid comm_semigroup
_inst_2: mul_action ↝
 -/
#print smul_assoc /- _inst_4: is_scalar_tower ↝
 -/
#print smul_smul /- _inst_2: mul_action ↝
 -/
#print one_smul /- _inst_2: mul_action ↝
 -/
#print function.injective.mul_action /- _inst_2: mul_action ↝
 -/
#print function.surjective.mul_action /- _inst_2: mul_action ↝
 -/
#print ite_smul /- _inst_2: mul_action ↝ has_scalar
 -/
#print smul_ite /- _inst_2: mul_action ↝ has_scalar
 -/
#print mul_action.is_scalar_tower.left /- _inst_2: mul_action ↝
 -/
#print mul_action.to_fun /- _inst_2: mul_action ↝
 -/
#print mul_action.to_fun_apply /- _inst_2: mul_action ↝
 -/
#print mul_action.comp_hom /- _inst_2: mul_action ↝
 -/
#print smul_one_smul /- _inst_3: mul_action ↝
_inst_5: is_scalar_tower ↝
 -/
#print smul_add /- _inst_3: distrib_mul_action ↝
 -/
#print smul_zero /- _inst_3: distrib_mul_action ↝
 -/
#print function.injective.distrib_mul_action /- _inst_3: distrib_mul_action ↝
 -/
#print function.surjective.distrib_mul_action /- _inst_3: distrib_mul_action ↝
 -/
#print const_smul_hom /- _inst_3: distrib_mul_action ↝
 -/
#print const_smul_hom_apply /- _inst_3: distrib_mul_action ↝
 -/
#print smul_neg /- _inst_3: distrib_mul_action ↝
 -/
#print smul_sub /- _inst_3: distrib_mul_action ↝
 -/

-- group_theory\group_action\group.lean
#print units.inv_smul_smul /- _inst_2: mul_action ↝
 -/
#print units.smul_inv_smul /- _inst_2: mul_action ↝
 -/
#print units.smul_perm_hom /- _inst_2: mul_action ↝
 -/
#print units.smul_left_cancel /- _inst_2: mul_action ↝
 -/
#print units.smul_eq_iff_eq_inv_smul /- _inst_2: mul_action ↝
 -/
#print is_unit.smul_left_cancel /- _inst_2: mul_action ↝
 -/
#print inv_smul_smul' /- _inst_2: mul_action ↝
 -/
#print smul_inv_smul' /- _inst_2: mul_action ↝
 -/
#print inv_smul_eq_iff' /- _inst_2: mul_action ↝
 -/
#print eq_inv_smul_iff' /- _inst_2: mul_action ↝
 -/
#print inv_smul_smul /- _inst_2: mul_action ↝
 -/
#print smul_inv_smul /- _inst_2: mul_action ↝
 -/
#print inv_smul_eq_iff /- _inst_2: mul_action ↝
 -/
#print eq_inv_smul_iff /- _inst_2: mul_action ↝
 -/
#print mul_action.to_perm /- _inst_2: mul_action ↝
 -/
#print mul_action.bijective /- _inst_2: mul_action ↝
 -/
#print units.smul_eq_zero /- _inst_3: distrib_mul_action ↝
 -/
#print units.smul_ne_zero /- _inst_3: distrib_mul_action ↝
 -/
#print is_unit.smul_eq_zero /- _inst_3: distrib_mul_action ↝
 -/

-- group_theory\monoid_localization.lean
#print localization.r /- _inst_1: comm_monoid ↝ monoid
 -/
#print add_localization.r /- _inst_1: add_comm_monoid ↝ add_monoid
 -/
#print submonoid.localization_map.mul_inv_left /- _inst_1: comm_monoid ↝ monoid
_inst_2: comm_monoid ↝ monoid comm_semigroup
 -/
#print add_submonoid.localization_map.add_neg_left /- _inst_1: add_comm_monoid ↝ add_monoid
_inst_2: add_comm_monoid ↝ add_monoid add_comm_semigroup
 -/
#print submonoid.localization_map.is_unit_comp /- _inst_3: comm_monoid ↝ monoid
 -/
#print add_submonoid.localization_map.is_unit_comp /- _inst_3: add_comm_monoid ↝ add_monoid
 -/

-- group_theory\order_of_element.lean
#print finset.mem_range_iff_mem_finset_range_of_mod_eq /- _inst_1: decidable_eq ↝
 -/
#print conj_injective /- _inst_1: group ↝ left_cancel_semigroup has_inv right_cancel_semigroup
 -/
#print order_of /- dec: decidable_eq ↝
 -/
#print pow_order_of_eq_one /- dec: decidable_eq ↝
 -/
#print order_of_pos /- dec: decidable_eq ↝
 -/
#print pow_injective_of_lt_order_of /- dec: decidable_eq ↝
 -/
#print order_of_le_card_univ /- dec: decidable_eq ↝
 -/
#print pow_eq_mod_order_of /- dec: decidable_eq ↝
 -/
#print gpow_eq_mod_order_of /- dec: decidable_eq ↝
 -/
#print mem_gpowers_iff_mem_range_order_of /- dec: decidable_eq ↝
 -/
#print decidable_gpowers /- dec: decidable_eq ↝
 -/
#print order_of_dvd_of_pow_eq_one /- dec: decidable_eq ↝
 -/
#print order_of_dvd_iff_pow_eq_one /- dec: decidable_eq ↝
 -/
#print order_of_le_of_pow_eq_one /- dec: decidable_eq ↝
 -/
#print sum_card_order_of_eq_card_pow_eq_one /- dec: decidable_eq ↝
 -/
#print order_eq_card_gpowers /- dec: decidable_eq ↝
 -/
#print order_of_one /- dec: decidable_eq ↝
 -/
#print order_of_eq_one_iff /- dec: decidable_eq ↝
 -/
#print order_of_eq_prime /- dec: decidable_eq ↝
 -/
#print order_of_dvd_card_univ /- dec: decidable_eq ↝
 -/
#print order_of_pow /- dec: decidable_eq ↝
 -/
#print image_range_order_of /- dec: decidable_eq ↝
 -/
#print is_cyclic_of_order_of_eq_card /- _inst_2: decidable_eq ↝
 -/
#print order_of_eq_card_of_forall_mem_gpowers /- _inst_2: decidable_eq ↝
 -/
#print is_cyclic.card_pow_eq_one_le /- _inst_2: decidable_eq ↝
 -/
#print is_cyclic.image_range_order_of /- _inst_2: decidable_eq ↝
 -/
#print is_cyclic.image_range_card /- _inst_2: decidable_eq ↝
 -/
#print card_pow_eq_one_eq_order_of_aux /- _inst_2: decidable_eq ↝
 -/
#print card_order_of_eq_totient_aux₂ /- _inst_2: decidable_eq ↝
 -/
#print is_cyclic_of_card_pow_eq_one_le /- _inst_2: decidable_eq ↝
 -/
#print is_cyclic.card_order_of_eq_totient /- _inst_3: decidable_eq ↝
 -/

-- group_theory\perm\cycles.lean
#print equiv.perm.same_cycle.decidable_rel /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_of /- _inst_1: decidable_eq ↝
_inst_2: fintype ↝
 -/
#print equiv.perm.cycle_of_apply /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_of_inv /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_of_pow_apply_self /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_of_gpow_apply_self /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_of_apply_of_same_cycle /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_of_apply_of_not_same_cycle /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_of_apply_self /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_of_cycle /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_of_one /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.is_cycle_cycle_of /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_factors_aux /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.cycle_factors /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.one_lt_nonfixed_point_card_of_ne_one /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.fixed_point_card_lt_of_ne_one /- _inst_1: decidable_eq ↝
 -/

-- group_theory\perm\sign.lean
#print equiv.perm.support /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.mem_support /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.is_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.swap_mul_eq_mul_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.mul_swap_eq_swap_mul /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.swap_mul_self_mul /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.swap_mul_eq_iff /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.is_swap_of_subtype /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.ne_and_ne_of_swap_mul_apply_ne_self /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.support_swap_mul_eq /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.card_support_swap_mul /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.swap_factors_aux /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.swap_factors /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.trunc_swap_factors /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.swap_induction_on /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.swap_mul_swap_mul_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.is_conj_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_aux2 /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_aux_eq_sign_aux2 /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_aux3 /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_aux3_mul_and_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_mul /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_one /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_refl /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_inv /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_swap' /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_eq_of_is_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_aux3_symm_trans_trans /- _inst_1: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print equiv.perm.sign_symm_trans_trans /- _inst_1: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print equiv.perm.sign_prod_list_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_surjective /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.eq_sign_of_surjective_hom /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_subtype_perm /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_of_subtype /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_eq_sign_of_equiv /- _inst_1: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print equiv.perm.sign_bij /- _inst_1: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print equiv.perm.is_cycle_swap /- _inst_3: decidable_eq ↝
 -/
#print equiv.perm.is_cycle_swap_mul_aux₁ /- _inst_3: decidable_eq ↝
 -/
#print equiv.perm.is_cycle_swap_mul_aux₂ /- _inst_3: decidable_eq ↝
 -/
#print equiv.perm.eq_swap_of_is_cycle_of_apply_apply_eq_self /- _inst_3: decidable_eq ↝
 -/
#print equiv.perm.is_cycle_swap_mul /- _inst_3: decidable_eq ↝
 -/
#print equiv.perm.support_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.card_support_swap /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_cycle /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.prod_prod_extend_right /- _inst_3: decidable_eq ↝
 -/
#print equiv.perm.sign_prod_extend_right /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_prod_congr_right /- _inst_1: decidable_eq ↝
 -/
#print equiv.perm.sign_prod_congr_left /- _inst_1: decidable_eq ↝
 -/

-- group_theory\subgroup.lean
#print subgroup.multiset_prod_mem /- _inst_3: comm_group ↝ group comm_monoid
 -/
#print add_subgroup.multiset_sum_mem /- _inst_3: add_comm_group ↝ add_comm_monoid add_group
 -/
#print subgroup.prod_mem /- _inst_3: comm_group ↝ group comm_monoid
 -/
#print add_subgroup.sum_mem /- _inst_3: add_comm_group ↝ add_comm_monoid add_group
 -/
#print add_subgroup.normal_of_comm /- _inst_3: add_comm_group ↝ add_comm_semigroup add_group
 -/
#print subgroup.normal_of_comm /- _inst_3: comm_group ↝ comm_semigroup group
 -/
#print monoid_hom.eq_of_eq_on_top /- _inst_3: group ↝ monoid
 -/
#print add_monoid_hom.eq_of_eq_on_top /- _inst_3: add_group ↝ add_monoid
 -/

-- group_theory\sylow.lean
#print mul_action.mem_fixed_points_iff_card_orbit_eq_one /- _inst_1: group ↝ monoid
_inst_2: mul_action ↝
 -/
#print mul_action.card_modeq_card_fixed_points /- _inst_2: mul_action ↝
 -/
#print sylow.mk_vector_prod_eq_one /- _inst_1: group ↝ has_inv has_one has_mul
 -/
#print sylow.vectors_prod_eq_one /- _inst_2: group ↝ has_one has_mul
 -/

-- linear_algebra\adic_completion.lean
#print adic_completion /- _inst_3: module ↝
 -/
#print Hausdorffification.of /- _inst_3: module ↝
 -/
#print Hausdorffification.induction_on /- _inst_3: module ↝
 -/
#print Hausdorffification.is_Hausdorff /- _inst_3: module ↝
 -/
#print Hausdorffification.lift /- _inst_3: module ↝
 -/
#print Hausdorffification.lift_of /- _inst_3: module ↝
 -/
#print Hausdorffification.lift_comp_of /- _inst_3: module ↝
 -/
#print Hausdorffification.lift_eq /- _inst_3: module ↝
 -/
#print adic_completion.of /- _inst_3: module ↝
 -/
#print adic_completion.of_apply /- _inst_3: module ↝
 -/
#print adic_completion.eval /- _inst_3: module ↝
 -/
#print adic_completion.coe_eval /- _inst_3: module ↝
 -/
#print adic_completion.eval_apply /- _inst_3: module ↝
 -/
#print adic_completion.eval_of /- _inst_3: module ↝
 -/
#print adic_completion.eval_comp_of /- _inst_3: module ↝
 -/
#print adic_completion.range_eval /- _inst_3: module ↝
 -/
#print adic_completion.ext /- _inst_3: module ↝
 -/
#print adic_completion.is_Hausdorff /- _inst_3: module ↝
 -/
#print is_adic_complete.of_subsingleton /- _inst_6: subsingleton ↝ is_Hausdorff is_precomplete
 -/

-- linear_algebra\affine_space\affine_equiv.lean
#print linear_equiv.to_affine_equiv /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_equiv.coe_to_affine_equiv /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.refl /- _inst_3: semimodule ↝
 -/
#print affine_equiv.coe_refl /- _inst_3: semimodule ↝
 -/
#print affine_equiv.refl_apply /- _inst_3: semimodule ↝
 -/
#print affine_equiv.to_equiv_refl /- _inst_3: semimodule ↝
 -/
#print affine_equiv.linear_refl /- _inst_3: semimodule ↝
 -/
#print affine_equiv.map_vadd /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.coe_to_equiv /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.to_affine_map /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.coe_to_affine_map /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.to_affine_map_mk /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.linear_to_affine_map /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.injective_to_affine_map /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.to_affine_map_inj /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.ext /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.injective_coe_fn /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.coe_fn_inj /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.injective_to_equiv /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.to_equiv_inj /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.mk' /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.coe_mk' /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.to_equiv_mk' /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.linear_mk' /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.symm /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.symm_to_equiv /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.symm_linear /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.bijective /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.surjective /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.injective /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.range_eq /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.apply_symm_apply /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.symm_apply_apply /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.apply_eq_iff_eq_symm_apply /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.apply_eq_iff_eq /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.symm_refl /- _inst_3: semimodule ↝
 -/
#print affine_equiv.trans /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
_inst_9: semimodule ↝
 -/
#print affine_equiv.coe_trans /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
_inst_9: semimodule ↝
 -/
#print affine_equiv.trans_apply /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
_inst_9: semimodule ↝
 -/
#print affine_equiv.trans_assoc /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
_inst_9: semimodule ↝
_inst_12: semimodule ↝
 -/
#print affine_equiv.trans_refl /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.refl_trans /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.trans_symm /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.symm_trans /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.apply_line_map /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
 -/
#print affine_equiv.group /- _inst_3: semimodule ↝
 -/
#print affine_equiv.one_def /- _inst_3: semimodule ↝
 -/
#print affine_equiv.coe_one /- _inst_3: semimodule ↝
 -/
#print affine_equiv.mul_def /- _inst_3: semimodule ↝
 -/
#print affine_equiv.coe_mul /- _inst_3: semimodule ↝
 -/
#print affine_equiv.inv_def /- _inst_3: semimodule ↝
 -/
#print affine_equiv.vadd_const /- _inst_3: semimodule ↝
 -/
#print affine_equiv.linear_vadd_const /- _inst_3: semimodule ↝
 -/
#print affine_equiv.vadd_const_apply /- _inst_3: semimodule ↝
 -/
#print affine_equiv.vadd_const_symm_apply /- _inst_3: semimodule ↝
 -/
#print affine_equiv.const_vsub /- _inst_3: semimodule ↝
 -/
#print affine_equiv.coe_const_vsub /- _inst_3: semimodule ↝
 -/
#print affine_equiv.coe_const_vsub_symm /- _inst_3: semimodule ↝
 -/
#print affine_equiv.const_vadd /- _inst_3: semimodule ↝
 -/
#print affine_equiv.linear_const_vadd /- _inst_3: semimodule ↝
 -/
#print affine_equiv.const_vadd_apply /- _inst_3: semimodule ↝
 -/
#print affine_equiv.const_vadd_symm_apply /- _inst_3: semimodule ↝
 -/
#print affine_equiv.point_reflection /- _inst_3: semimodule ↝
 -/
#print affine_equiv.point_reflection_apply /- _inst_3: semimodule ↝
 -/
#print affine_equiv.point_reflection_symm /- _inst_3: semimodule ↝
 -/
#print affine_equiv.to_equiv_point_reflection /- _inst_3: semimodule ↝
 -/
#print affine_equiv.point_reflection_self /- _inst_3: semimodule ↝
 -/
#print affine_equiv.point_reflection_involutive /- _inst_3: semimodule ↝
 -/
#print affine_equiv.point_reflection_fixed_iff_of_injective_bit0 /- _inst_3: semimodule ↝
 -/
#print affine_equiv.injective_point_reflection_left_of_injective_bit0 /- _inst_3: semimodule ↝
 -/
#print affine_equiv.injective_point_reflection_left_of_module /- _inst_3: semimodule ↝
 -/
#print affine_equiv.point_reflection_fixed_iff_of_module /- _inst_3: semimodule ↝
 -/
#print affine_map.line_map_vadd /- _inst_3: semimodule ↝
 -/
#print affine_map.line_map_vsub /- _inst_3: semimodule ↝
 -/
#print affine_map.vsub_line_map /- _inst_3: semimodule ↝
 -/
#print affine_map.vadd_line_map /- _inst_3: semimodule ↝
 -/
#print affine_map.homothety_neg_one_apply /- _inst_15: semimodule ↝
 -/

-- linear_algebra\affine_space\affine_map.lean
#print affine_map.line_map_apply_module /- _inst_3: module ↝
 -/
#print affine_map.line_map_same_apply /- _inst_3: module ↝
 -/
#print affine_map.line_map_apply_one /- _inst_3: module ↝
 -/
#print affine_map.left_vsub_line_map /- _inst_3: module ↝
 -/
#print affine_map.coe_smul /- _inst_1: comm_ring ↝ ring
 -/
#print affine_map.homothety /- _inst_1: comm_ring ↝ ring
 -/
#print affine_map.homothety_one /- _inst_3: module ↝
 -/
#print affine_map.homothety_mul /- _inst_3: module ↝
 -/

-- linear_algebra\affine_space\affine_subspace.lean
#print affine_subspace.vadd_mem_of_mem_direction /- _inst_3: module ↝
 -/

-- linear_algebra\affine_space\combination.lean
#print finset.weighted_vsub_of_point /- S: add_torsor ↝ has_vsub
 -/
#print finset.weighted_vsub_of_point_eq_of_sum_eq_zero /- _inst_3: module ↝
 -/
#print finset.weighted_vsub_of_point_vadd_eq_of_sum_eq_one /- _inst_3: module ↝
 -/
#print finset.weighted_vsub_of_point_erase /- _inst_3: module ↝
 -/
#print finset.weighted_vsub_of_point_insert /- _inst_3: module ↝
 -/
#print finset.affine_combination_of_eq_one_of_eq_zero /- _inst_3: module ↝
 -/
#print finset.centroid_weights /- _inst_1: division_ring ↝ has_inv has_one has_zero has_add
 -/
#print finset.centroid_singleton /- _inst_3: module ↝
 -/
#print finset.centroid_insert_singleton /- _inst_3: module ↝
 -/
#print mem_vector_span_iff_eq_weighted_vsub /- _inst_3: module ↝
 -/
#print affine_map.weighted_vsub_of_point /- _inst_3: module ↝
 -/

-- linear_algebra\affine_space\finite_dimensional.lean
#print finite_dimensional_vector_span_of_finite /- _inst_3: module ↝
 -/
#print finite_dimensional_vector_span_of_fintype /- _inst_3: module ↝
 -/
#print finite_dimensional_vector_span_image_of_fintype /- _inst_3: module ↝
 -/
#print finite_dimensional_direction_affine_span_of_finite /- _inst_3: module ↝
 -/
#print finite_dimensional_direction_affine_span_of_fintype /- _inst_3: module ↝
 -/
#print finite_dimensional_direction_affine_span_image_of_fintype /- _inst_3: module ↝
 -/
#print findim_vector_span_image_finset_of_affine_independent /- _inst_3: module ↝
 -/
#print findim_vector_span_of_affine_independent /- _inst_3: module ↝
 -/
#print vector_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one /- _inst_3: module ↝
 -/
#print vector_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one /- _inst_3: module ↝
 -/
#print affine_span_image_finset_eq_of_le_of_affine_independent_of_card_eq_findim_add_one /- _inst_3: module ↝
 -/
#print affine_span_eq_of_le_of_affine_independent_of_card_eq_findim_add_one /- _inst_3: module ↝
 -/
#print affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one /- _inst_3: module ↝ finite_dimensional
 -/
#print findim_vector_span_image_finset_le /- _inst_3: module ↝
 -/
#print findim_vector_span_range_le /- _inst_3: module ↝
 -/
#print affine_independent_iff_findim_vector_span_eq /- _inst_3: module ↝
 -/
#print affine_independent_iff_le_findim_vector_span /- _inst_3: module ↝
 -/
#print affine_independent_iff_not_findim_vector_span_le /- _inst_3: module ↝
 -/
#print findim_vector_span_le_iff_not_affine_independent /- _inst_3: module ↝
 -/
#print collinear /- _inst_3: module ↝
 -/
#print collinear_iff_dim_le_one /- _inst_3: module ↝
 -/
#print collinear_iff_findim_le_one /- _inst_3: module ↝
 -/
#print collinear_empty /- _inst_3: module ↝
 -/
#print collinear_singleton /- _inst_3: module ↝
 -/
#print collinear_iff_of_mem /- _inst_3: module ↝
 -/
#print collinear_insert_singleton /- _inst_3: module ↝
 -/
#print affine_independent_iff_not_collinear /- _inst_3: module ↝ finite_dimensional
 -/
#print collinear_iff_not_affine_independent /- _inst_3: module ↝ finite_dimensional
 -/

-- linear_algebra\affine_space\midpoint.lean
#print midpoint /- _inst_4: semimodule ↝
 -/
#print affine_map.map_midpoint /- _inst_4: semimodule ↝
_inst_7: semimodule ↝
 -/
#print affine_equiv.map_midpoint /- _inst_4: semimodule ↝
_inst_7: semimodule ↝
 -/
#print affine_equiv.point_reflection_midpoint_left /- _inst_4: semimodule ↝
 -/
#print midpoint_comm /- _inst_4: semimodule ↝
 -/
#print affine_equiv.point_reflection_midpoint_right /- _inst_4: semimodule ↝
 -/
#print midpoint_vsub_midpoint /- _inst_4: semimodule ↝
 -/
#print midpoint_vadd_midpoint /- _inst_4: semimodule ↝
 -/
#print midpoint_eq_iff /- _inst_4: semimodule ↝
 -/
#print midpoint_eq_midpoint_iff_vsub_eq_vsub /- _inst_4: semimodule ↝
 -/
#print midpoint_eq_iff' /- _inst_4: semimodule ↝
 -/
#print midpoint_unique /- _inst_4: semimodule ↝
_inst_11: semimodule ↝
 -/
#print midpoint_self /- _inst_4: semimodule ↝
 -/
#print midpoint_add_self /- _inst_4: semimodule ↝
 -/
#print midpoint_zero_add /- _inst_4: semimodule ↝
 -/
#print line_map_inv_two /- _inst_1: division_ring ↝ invertible has_inv ring
_inst_2: char_zero ↝ invertible
_inst_4: semimodule ↝
 -/
#print line_map_one_half /- _inst_4: semimodule ↝
 -/
#print homothety_inv_of_two /- _inst_4: semimodule ↝
 -/
#print homothety_inv_two /- _inst_1: field ↝ invertible has_inv comm_ring
_inst_2: char_zero ↝ invertible
_inst_4: semimodule ↝
 -/
#print homothety_one_half /- _inst_4: semimodule ↝
 -/
#print pi_midpoint_apply /- _inst_1: field ↝ ring
 -/
#print add_monoid_hom.of_map_midpoint /- _inst_4: semimodule ↝
_inst_8: semimodule ↝
 -/
#print add_monoid_hom.coe_of_map_midpoint /- _inst_4: semimodule ↝
_inst_8: semimodule ↝
 -/

-- linear_algebra\affine_space\ordered.lean
#print slope /- _inst_1: field ↝ has_sub has_inv semiring
_inst_2: add_comm_group ↝ add_comm_monoid has_vsub add_group
_inst_3: semimodule ↝ has_scalar
_inst_4: add_torsor ↝ has_vsub
 -/
#print slope_same /- _inst_3: semimodule ↝
 -/
#print eq_of_slope_eq_zero /- _inst_3: semimodule ↝
 -/
#print slope_comm /- _inst_3: semimodule ↝
 -/
#print sub_div_sub_smul_slope_add_sub_div_sub_smul_slope /- _inst_3: semimodule ↝
 -/
#print line_map_slope_slope_sub_div_sub /- _inst_3: semimodule ↝
 -/
#print line_map_slope_line_map_slope_line_map /- _inst_3: semimodule ↝
 -/
#print line_map_mono_left /- _inst_1: ordered_ring ↝ ordered_semiring ring ordered_add_comm_group
_inst_2: ordered_add_comm_group ↝ ordered_add_comm_monoid add_comm_group
_inst_3: semimodule ↝
 -/
#print line_map_strict_mono_left /- _inst_1: ordered_ring ↝ ordered_semiring ring ordered_add_comm_group
_inst_2: ordered_add_comm_group ↝ add_comm_group ordered_cancel_add_comm_monoid
_inst_3: semimodule ↝
 -/
#print line_map_mono_right /- _inst_1: ordered_ring ↝ ordered_semiring ring
_inst_2: ordered_add_comm_group ↝ ordered_add_comm_monoid add_comm_group
_inst_3: semimodule ↝
 -/
#print line_map_strict_mono_right /- _inst_1: ordered_ring ↝ ordered_semiring ring
_inst_2: ordered_add_comm_group ↝ add_comm_group ordered_cancel_add_comm_monoid
_inst_3: semimodule ↝
 -/
#print line_map_mono_endpoints /- _inst_3: semimodule ↝
 -/
#print line_map_strict_mono_endpoints /- _inst_3: semimodule ↝
 -/
#print line_map_lt_line_map_iff_of_lt /- _inst_1: ordered_ring ↝ ordered_semiring ring ordered_add_comm_group
_inst_3: semimodule ↝
 -/
#print left_lt_line_map_iff_lt /- _inst_3: semimodule ↝
 -/
#print line_map_lt_left_iff_lt /- _inst_3: semimodule ↝
 -/
#print line_map_lt_right_iff_lt /- _inst_3: semimodule ↝
 -/
#print right_lt_line_map_iff_lt /- _inst_3: semimodule ↝
 -/
#print line_map_le_line_map_iff_of_lt /- _inst_3: semimodule ↝
 -/
#print left_le_line_map_iff_le /- _inst_3: semimodule ↝
 -/
#print left_le_midpoint /- _inst_3: semimodule ↝
 -/
#print line_map_le_left_iff_le /- _inst_3: semimodule ↝
 -/
#print midpoint_le_left /- _inst_3: semimodule ↝
 -/
#print line_map_le_right_iff_le /- _inst_3: semimodule ↝
 -/
#print midpoint_le_right /- _inst_3: semimodule ↝
 -/
#print right_le_line_map_iff_le /- _inst_3: semimodule ↝
 -/
#print right_le_midpoint /- _inst_3: semimodule ↝
 -/
#print map_le_line_map_iff_slope_le_slope_left /- _inst_3: semimodule ↝
 -/
#print line_map_le_map_iff_slope_le_slope_left /- _inst_3: semimodule ↝
 -/
#print map_lt_line_map_iff_slope_lt_slope_left /- _inst_3: semimodule ↝
 -/
#print line_map_lt_map_iff_slope_lt_slope_left /- _inst_3: semimodule ↝
 -/
#print map_le_line_map_iff_slope_le_slope_right /- _inst_3: semimodule ↝
 -/
#print line_map_le_map_iff_slope_le_slope_right /- _inst_3: semimodule ↝
 -/
#print map_lt_line_map_iff_slope_lt_slope_right /- _inst_3: semimodule ↝
 -/
#print line_map_lt_map_iff_slope_lt_slope_right /- _inst_3: semimodule ↝
 -/
#print map_le_line_map_iff_slope_le_slope /- _inst_3: semimodule ↝
 -/
#print line_map_le_map_iff_slope_le_slope /- _inst_3: semimodule ↝
 -/
#print map_lt_line_map_iff_slope_lt_slope /- _inst_3: semimodule ↝
 -/
#print line_map_lt_map_iff_slope_lt_slope /- _inst_3: semimodule ↝
 -/

-- linear_algebra\basic.lean
#print finsupp.smul_sum /- _inst_4: semimodule ↝
 -/
#print linear_map.comp_id /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.id_comp /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.comp_assoc /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.dom_restrict /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.dom_restrict_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.cod_restrict /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.cod_restrict_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.comp_cod_restrict /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.subtype_comp_cod_restrict /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.restrict /- _inst_6: semimodule ↝
 -/
#print linear_map.restrict_apply /- _inst_6: semimodule ↝
 -/
#print linear_map.subtype_comp_restrict /- _inst_6: semimodule ↝
 -/
#print linear_map.restrict_eq_cod_restrict_dom_restrict /- _inst_6: semimodule ↝
 -/
#print linear_map.restrict_eq_dom_restrict_cod_restrict /- _inst_6: semimodule ↝
 -/
#print linear_map.has_zero /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.inhabited /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.zero_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.default_def /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.unique_of_left /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.unique_of_right /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.has_add /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.add_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.add_comm_monoid /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.linear_map_apply_is_add_monoid_hom /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.add_comp /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.comp_add /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.sum_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.smul_right /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.smul_right_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.has_one /- _inst_6: semimodule ↝
 -/
#print linear_map.has_mul /- _inst_6: semimodule ↝
 -/
#print linear_map.mul_eq_comp /- _inst_6: semimodule ↝
 -/
#print linear_map.one_app /- _inst_6: semimodule ↝
 -/
#print linear_map.mul_app /- _inst_6: semimodule ↝
 -/
#print linear_map.comp_zero /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.zero_comp /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.coe_fn_sum /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.monoid /- _inst_6: semimodule ↝
 -/
#print linear_map.pi_apply_eq_sum_univ /- _inst_6: semimodule ↝
 -/
#print linear_map.fst /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.snd /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.fst_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.snd_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.prod /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.prod_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.fst_prod /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.snd_prod /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.pair_fst_snd /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.inl /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.inr /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.inl_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.inr_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.inl_injective /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.inr_injective /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.coprod /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.coprod_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.coprod_inl /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.coprod_inr /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.coprod_inl_inr /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.fst_eq_coprod /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.snd_eq_coprod /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.inl_eq_prod /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.inr_eq_prod /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.prod_map /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.prod_map_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.has_neg /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.neg_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.comp_neg /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.add_comm_group /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.linear_map_apply_is_add_group_hom /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.sub_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.sub_comp /- _inst_3: add_comm_group ↝ add_comm_monoid
_inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.comp_sub /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.has_scalar /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_9: distrib_mul_action ↝
_inst_10: smul_comm_class ↝
 -/
#print linear_map.smul_apply /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_9: distrib_mul_action ↝ has_scalar
_inst_10: smul_comm_class ↝ has_scalar
 -/
#print linear_map.distrib_mul_action /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_9: distrib_mul_action ↝
_inst_10: smul_comm_class ↝
 -/
#print linear_map.smul_comp /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: distrib_mul_action ↝ has_scalar
_inst_10: smul_comm_class ↝ has_scalar
 -/
#print linear_map.semimodule /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_9: semimodule ↝
_inst_11: smul_comm_class ↝
 -/
#print linear_map.applyₗ' /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_9: semimodule ↝
_inst_11: smul_comm_class ↝
 -/
#print linear_map.comp_smul /- _inst_1: comm_semiring ↝ semiring
_inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.comp_right /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.applyₗ /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.endomorphism_semiring /- _inst_3: semimodule ↝
 -/
#print linear_map.mul_apply /- _inst_3: semimodule ↝
 -/
#print linear_map.endomorphism_ring /- _inst_3: semimodule ↝
 -/
#print linear_map.smul_rightₗ /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.smul_rightₗ_apply /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.partial_order /- _inst_5: semimodule ↝
 -/
#print submodule.le_def /- _inst_5: semimodule ↝
 -/
#print submodule.le_def' /- _inst_5: semimodule ↝
 -/
#print submodule.lt_def /- _inst_5: semimodule ↝
 -/
#print submodule.not_le_iff_exists /- _inst_5: semimodule ↝
 -/
#print submodule.exists_of_lt /- _inst_5: semimodule ↝
 -/
#print submodule.lt_iff_le_and_exists /- _inst_5: semimodule ↝
 -/
#print submodule.of_le /- _inst_5: semimodule ↝
 -/
#print submodule.coe_of_le /- _inst_5: semimodule ↝
 -/
#print submodule.of_le_apply /- _inst_5: semimodule ↝
 -/
#print submodule.subtype_comp_of_le /- _inst_5: semimodule ↝
 -/
#print submodule.has_bot /- _inst_5: semimodule ↝
 -/
#print submodule.inhabited' /- _inst_5: semimodule ↝
 -/
#print submodule.bot_coe /- _inst_5: semimodule ↝
 -/
#print submodule.mem_bot /- _inst_5: semimodule ↝
 -/
#print submodule.nonzero_mem_of_bot_lt /- _inst_5: semimodule ↝
 -/
#print submodule.order_bot /- _inst_5: semimodule ↝
 -/
#print submodule.eq_bot_iff /- _inst_5: semimodule ↝
 -/
#print submodule.ne_bot_iff /- _inst_5: semimodule ↝
 -/
#print submodule.has_top /- _inst_5: semimodule ↝
 -/
#print submodule.top_coe /- _inst_5: semimodule ↝
 -/
#print submodule.mem_top /- _inst_5: semimodule ↝
 -/
#print submodule.eq_bot_of_zero_eq_one /- _inst_5: semimodule ↝
 -/
#print submodule.order_top /- _inst_5: semimodule ↝
 -/
#print submodule.has_Inf /- _inst_5: semimodule ↝
 -/
#print submodule.has_inf /- _inst_5: semimodule ↝
 -/
#print submodule.complete_lattice /- _inst_5: semimodule ↝
 -/
#print submodule.add_comm_monoid_submodule /- _inst_5: semimodule ↝
 -/
#print submodule.add_eq_sup /- _inst_5: semimodule ↝
 -/
#print submodule.zero_eq_bot /- _inst_5: semimodule ↝
 -/
#print submodule.eq_top_iff' /- _inst_5: semimodule ↝
 -/
#print submodule.bot_ne_top /- _inst_5: semimodule ↝
 -/
#print submodule.inf_coe /- _inst_5: semimodule ↝
 -/
#print submodule.mem_inf /- _inst_5: semimodule ↝
 -/
#print submodule.Inf_coe /- _inst_5: semimodule ↝
 -/
#print submodule.infi_coe /- _inst_5: semimodule ↝
 -/
#print submodule.mem_Inf /- _inst_5: semimodule ↝
 -/
#print submodule.mem_infi /- _inst_5: semimodule ↝
 -/
#print submodule.disjoint_def /- _inst_5: semimodule ↝
 -/
#print submodule.disjoint_def' /- _inst_5: semimodule ↝
 -/
#print submodule.mem_right_iff_eq_zero_of_disjoint /- _inst_5: semimodule ↝
 -/
#print submodule.mem_left_iff_eq_zero_of_disjoint /- _inst_5: semimodule ↝
 -/
#print submodule.map /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_coe /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.mem_map /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.mem_map_of_mem /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_id /- _inst_5: semimodule ↝
 -/
#print submodule.map_comp /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print submodule.map_mono /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_zero /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.comap /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.comap_coe /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.mem_comap /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.comap_id /- _inst_5: semimodule ↝
 -/
#print submodule.comap_comp /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print submodule.comap_mono /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_le_iff_le_comap /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.gc_map_comap /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_bot /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_sup /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_supr /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.comap_top /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.comap_inf /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.comap_infi /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.comap_zero /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_comap_le /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.le_comap_map /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_inf_eq_map_inf_comap /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.map_comap_subtype /- _inst_5: semimodule ↝
 -/
#print submodule.eq_zero_of_bot_submodule /- _inst_5: semimodule ↝
 -/
#print submodule.span /- _inst_5: semimodule ↝
 -/
#print submodule.mem_span /- _inst_5: semimodule ↝
 -/
#print submodule.subset_span /- _inst_5: semimodule ↝
 -/
#print submodule.span_le /- _inst_5: semimodule ↝
 -/
#print submodule.span_mono /- _inst_5: semimodule ↝
 -/
#print submodule.span_eq_of_le /- _inst_5: semimodule ↝
 -/
#print submodule.span_eq /- _inst_5: semimodule ↝
 -/
#print submodule.map_span /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.span_induction /- _inst_5: semimodule ↝
 -/
#print submodule.gi /- _inst_5: semimodule ↝
 -/
#print submodule.span_empty /- _inst_5: semimodule ↝
 -/
#print submodule.span_univ /- _inst_5: semimodule ↝
 -/
#print submodule.span_union /- _inst_5: semimodule ↝
 -/
#print submodule.span_Union /- _inst_5: semimodule ↝
 -/
#print submodule.coe_supr_of_directed /- _inst_5: semimodule ↝
 -/
#print submodule.mem_sup_left /- _inst_5: semimodule ↝
 -/
#print submodule.mem_sup_right /- _inst_5: semimodule ↝
 -/
#print submodule.mem_supr_of_mem /- _inst_5: semimodule ↝
 -/
#print submodule.mem_Sup_of_mem /- _inst_5: semimodule ↝
 -/
#print submodule.mem_supr_of_directed /- _inst_5: semimodule ↝
 -/
#print submodule.mem_Sup_of_directed /- _inst_5: semimodule ↝
 -/
#print submodule.mem_sup /- _inst_5: semimodule ↝
 -/
#print submodule.mem_sup' /- _inst_5: semimodule ↝
 -/
#print submodule.mem_span_singleton_self /- _inst_5: semimodule ↝
 -/
#print submodule.nontrivial_span_singleton /- _inst_5: semimodule ↝
 -/
#print submodule.mem_span_singleton /- _inst_5: semimodule ↝
 -/
#print submodule.le_span_singleton_iff /- _inst_5: semimodule ↝
 -/
#print submodule.span_singleton_eq_range /- _inst_5: semimodule ↝
 -/
#print submodule.span_singleton_smul_le /- _inst_5: semimodule ↝
 -/
#print submodule.span_singleton_smul_eq /- _inst_8: division_ring ↝ group_with_zero ring
_inst_10: module ↝
 -/
#print submodule.disjoint_span_singleton /- _inst_10: module ↝
 -/
#print submodule.mem_span_insert /- _inst_5: semimodule ↝
 -/
#print submodule.span_insert_eq_span /- _inst_5: semimodule ↝
 -/
#print submodule.span_span /- _inst_5: semimodule ↝
 -/
#print submodule.span_eq_bot /- _inst_5: semimodule ↝
 -/
#print submodule.span_singleton_eq_bot /- _inst_5: semimodule ↝
 -/
#print submodule.span_zero /- _inst_5: semimodule ↝
 -/
#print submodule.span_image /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.supr_eq_span /- _inst_5: semimodule ↝
 -/
#print submodule.span_singleton_le_iff_mem /- _inst_5: semimodule ↝
 -/
#print submodule.lt_add_iff_not_mem /- _inst_5: semimodule ↝
 -/
#print submodule.mem_supr /- _inst_5: semimodule ↝
 -/
#print submodule.prod /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.prod_coe /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.mem_prod /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.span_prod_le /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.prod_top /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.prod_bot /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.prod_mono /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.prod_inf_prod /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.prod_sup_prod /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.neg_coe /- _inst_5: semimodule ↝
 -/
#print submodule.map_neg /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.span_neg /- _inst_5: semimodule ↝
 -/
#print submodule.mem_span_insert' /- _inst_5: semimodule ↝
 -/
#print submodule.quotient_rel /- _inst_5: semimodule ↝
 -/
#print submodule.quotient /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.mk /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.mk_eq_mk /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.mk'_eq_mk /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.quot_mk_eq_mk /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.eq /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.has_zero /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.inhabited /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.mk_zero /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.mk_eq_zero /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.has_add /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.mk_add /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.has_neg /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.mk_neg /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.add_comm_group /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.has_scalar /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.mk_smul /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.semimodule /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.mk_surjective /- _inst_5: semimodule ↝
 -/
#print submodule.quotient.nontrivial_of_lt_top /- _inst_5: semimodule ↝
 -/
#print submodule.quot_hom_ext /- _inst_3: add_comm_group ↝ add_comm_monoid
_inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print submodule.comap_smul /- _inst_5: vector_space ↝
 -/
#print submodule.comap_smul' /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
 -/
#print submodule.map_smul' /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
 -/
#print linear_map.eq_on_span /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.eq_on_span' /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ext_on /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ext_on_range /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.finsupp_sum /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_cod_restrict /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.comap_cod_restrict /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_coe /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.mem_range /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.mem_range_self /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_id /- _inst_5: semimodule ↝
 -/
#print linear_map.range_comp /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.range_comp_le_range /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.range_eq_top /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_le_iff_comap /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_le_range /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_coprod /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.is_compl_range_inl_inr /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.sup_range_inl_inr /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_restrict /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.to_span_singleton /- _inst_5: semimodule ↝
 -/
#print linear_map.span_singleton_eq_range /- _inst_5: semimodule ↝
 -/
#print linear_map.to_span_singleton_one /- _inst_5: semimodule ↝
 -/
#print linear_map.ker /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.mem_ker /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ker_id /- _inst_5: semimodule ↝
 -/
#print linear_map.map_coe_ker /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.comp_ker_subtype /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ker_comp /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.ker_le_ker_comp /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.disjoint_ker /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.disjoint_inl_inr /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ker_eq_bot' /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.le_ker_iff_map /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ker_cod_restrict /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_cod_restrict /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ker_restrict /- _inst_5: semimodule ↝
 -/
#print linear_map.map_comap_eq /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_comap_eq_self /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ker_zero /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_zero /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ker_eq_top /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_le_bot_iff /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_le_ker_iff /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.comap_le_comap_iff /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.comap_injective /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_coprod_prod /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.comap_prod_prod /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.prod_eq_inf_comap /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.prod_eq_sup_map /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.span_inl_union_inr /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ker_prod /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.range_prod_le /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.ker_eq_bot_of_injective /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.comap_map_eq /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.comap_map_eq_self /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_le_map_iff /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_le_map_iff' /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_injective /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.map_eq_top_iff /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.sub_mem_ker_iff /- _inst_1: ring ↝ semiring
_inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.disjoint_ker' /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.inj_of_disjoint_ker /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.ker_eq_bot /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_map.range_prod_eq /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print submodule.sup_eq_range /- _inst_3: semimodule ↝
 -/
#print is_linear_map.is_linear_map_add /- _inst_3: semimodule ↝
 -/
#print is_linear_map.is_linear_map_sub /- _inst_3: semimodule ↝
 -/
#print submodule.map_top /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.comap_bot /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.ker_subtype /- _inst_3: semimodule ↝
 -/
#print submodule.range_subtype /- _inst_3: semimodule ↝
 -/
#print submodule.map_subtype_le /- _inst_3: semimodule ↝
 -/
#print submodule.map_subtype_top /- _inst_3: semimodule ↝
 -/
#print submodule.comap_subtype_eq_top /- _inst_3: semimodule ↝
 -/
#print submodule.comap_subtype_self /- _inst_3: semimodule ↝
 -/
#print submodule.ker_of_le /- _inst_3: semimodule ↝
 -/
#print submodule.range_of_le /- _inst_3: semimodule ↝
 -/
#print submodule.map_inl /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.map_inr /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.comap_fst /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.comap_snd /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.prod_comap_inl /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.prod_comap_inr /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.prod_map_fst /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.prod_map_snd /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.ker_inl /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.ker_inr /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.range_fst /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.range_snd /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.disjoint_iff_comap_eq_bot /- _inst_3: semimodule ↝
 -/
#print submodule.map_subtype.rel_iso /- _inst_3: semimodule ↝
 -/
#print submodule.map_subtype.order_embedding /- _inst_3: semimodule ↝
 -/
#print submodule.map_subtype_embedding_eq /- _inst_3: semimodule ↝
 -/
#print submodule.mkq /- _inst_3: semimodule ↝
 -/
#print submodule.mkq_apply /- _inst_3: semimodule ↝
 -/
#print submodule.liftq /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.liftq_apply /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.liftq_mkq /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.range_mkq /- _inst_3: semimodule ↝
 -/
#print submodule.ker_mkq /- _inst_3: semimodule ↝
 -/
#print submodule.le_comap_mkq /- _inst_3: semimodule ↝
 -/
#print submodule.mkq_map_self /- _inst_3: semimodule ↝
 -/
#print submodule.comap_map_mkq /- _inst_3: semimodule ↝
 -/
#print submodule.map_mkq_eq_top /- _inst_3: semimodule ↝
 -/
#print submodule.mapq /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.mapq_apply /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.mapq_mkq /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.comap_liftq /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.map_liftq /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.ker_liftq /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.range_liftq /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.ker_liftq_eq_bot /- _inst_3: semimodule ↝
_inst_4: semimodule ↝
 -/
#print submodule.comap_mkq.rel_iso /- _inst_3: semimodule ↝
 -/
#print submodule.comap_mkq.order_embedding /- _inst_3: semimodule ↝
 -/
#print submodule.comap_mkq_embedding_eq /- _inst_3: semimodule ↝
 -/
#print linear_map.range_mkq_comp /- _inst_6: module ↝
 -/
#print linear_map.ker_le_range_iff /- _inst_6: module ↝
 -/
#print linear_map.ker_eq_bot_of_cancel /- _inst_5: module ↝
 -/
#print linear_map.range_eq_top_of_cancel /- _inst_6: module ↝
 -/
#print linear_map.range_range_restrict /- _inst_4: semimodule ↝
_inst_5: semimodule ↝
 -/
#print linear_equiv.eq_bot_of_equiv /- _inst_6: semimodule ↝
 -/
#print linear_equiv.neg /- _inst_3: semimodule ↝
 -/
#print linear_equiv.coe_neg /- _inst_3: semimodule ↝
 -/
#print linear_equiv.neg_apply /- _inst_3: semimodule ↝
 -/
#print linear_equiv.symm_neg /- _inst_3: semimodule ↝
 -/
#print linear_equiv.smul_of_unit /- _inst_5: semimodule ↝
 -/
#print linear_equiv.arrow_congr /- _inst_13: module ↝
_inst_14: module ↝
_inst_15: module ↝
_inst_16: module ↝
 -/
#print linear_equiv.arrow_congr_apply /- _inst_13: module ↝
_inst_14: module ↝
_inst_15: module ↝
_inst_16: module ↝
 -/
#print linear_equiv.arrow_congr_symm_apply /- _inst_13: module ↝
_inst_14: module ↝
_inst_15: module ↝
_inst_16: module ↝
 -/
#print linear_equiv.arrow_congr_comp /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_11: module ↝
_inst_12: module ↝
_inst_13: module ↝
 -/
#print linear_equiv.arrow_congr_trans /- _inst_9: module ↝
_inst_11: module ↝
_inst_13: module ↝
_inst_15: module ↝
_inst_17: module ↝
_inst_19: module ↝
 -/
#print linear_equiv.congr_right /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.conj /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_equiv.conj_apply /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_equiv.symm_conj_apply /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_equiv.conj_comp /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_equiv.conj_trans /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_equiv.conj_id /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
 -/
#print linear_equiv.smul_of_ne_zero /- _inst_1: field ↝ group_with_zero comm_ring
 -/
#print linear_equiv.ker_to_span_singleton /- _inst_1: field ↝ group_with_zero ring
_inst_5: module ↝
 -/
#print linear_equiv.to_span_nonzero_singleton /- _inst_5: module ↝
 -/
#print linear_equiv.to_span_nonzero_singleton_one /- _inst_5: module ↝
 -/
#print linear_equiv.coord /- _inst_5: module ↝
 -/
#print linear_equiv.coord_self /- _inst_5: module ↝
 -/
#print submodule.comap_subtype_equiv_of_le /- _inst_3: semimodule ↝
 -/
#print submodule.quot_equiv_of_eq_bot /- _inst_3: module ↝
 -/
#print submodule.quot_equiv_of_eq_bot_apply_mk /- _inst_3: module ↝
 -/
#print submodule.quot_equiv_of_eq_bot_symm_apply /- _inst_3: module ↝
 -/
#print submodule.coe_quot_equiv_of_eq_bot_symm /- _inst_3: module ↝
 -/
#print submodule.quot_equiv_of_eq /- _inst_3: module ↝
 -/
#print submodule.mem_map_equiv /- _inst_1: comm_ring ↝ ring
 -/
#print submodule.comap_le_comap_smul /- _inst_1: comm_ring ↝ ring
 -/
#print submodule.inf_comap_le_comap_add /- _inst_1: comm_ring ↝ ring
 -/
#print submodule.compatible_maps /- _inst_4: module ↝
_inst_5: module ↝
 -/
#print submodule.mapq_linear /- _inst_4: module ↝
_inst_5: module ↝
 -/
#print equiv.to_linear_equiv /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print add_equiv.to_linear_equiv /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print add_equiv.coe_to_linear_equiv /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print add_equiv.coe_to_linear_equiv_symm /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print linear_map.quot_ker_equiv_range /- _inst_5: module ↝
_inst_6: module ↝
 -/
#print linear_map.quot_ker_equiv_range_apply_mk /- _inst_5: module ↝
_inst_6: module ↝
 -/
#print linear_map.quot_ker_equiv_range_symm_apply_image /- _inst_5: module ↝
_inst_6: module ↝
 -/
#print linear_map.quotient_inf_to_sup_quotient /- _inst_5: module ↝
 -/
#print linear_map.quotient_inf_equiv_sup_quotient /- _inst_5: module ↝
 -/
#print linear_map.coe_quotient_inf_to_sup_quotient /- _inst_5: module ↝
 -/
#print linear_map.quotient_inf_equiv_sup_quotient_apply_mk /- _inst_5: module ↝
 -/
#print linear_map.quotient_inf_equiv_sup_quotient_symm_apply_left /- _inst_5: module ↝
 -/
#print linear_map.quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff /- _inst_5: module ↝
 -/
#print linear_map.quotient_inf_equiv_sup_quotient_symm_apply_right /- _inst_5: module ↝
 -/
#print linear_map.is_linear_map_prod_iso /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: semimodule ↝
 -/
#print linear_map.pi /- _inst_3: semimodule ↝
 -/
#print linear_map.pi_apply /- _inst_3: semimodule ↝
 -/
#print linear_map.ker_pi /- _inst_3: semimodule ↝
 -/
#print linear_map.pi_eq_zero /- _inst_3: semimodule ↝
 -/
#print linear_map.pi_zero /- _inst_3: semimodule ↝
 -/
#print linear_map.pi_comp /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print linear_map.proj_pi /- _inst_3: semimodule ↝
 -/
#print linear_map.diag /- _inst_8: decidable_eq ↝
 -/
#print linear_map.update_apply /- _inst_3: semimodule ↝
_inst_8: decidable_eq ↝
 -/
#print linear_map.std_basis /- _inst_8: decidable_eq ↝
 -/
#print linear_map.std_basis_apply /- _inst_8: decidable_eq ↝
 -/
#print linear_map.std_basis_same /- _inst_8: decidable_eq ↝
 -/
#print linear_map.std_basis_ne /- _inst_8: decidable_eq ↝
 -/
#print linear_map.ker_std_basis /- _inst_8: decidable_eq ↝
 -/
#print linear_map.proj_comp_std_basis /- _inst_8: decidable_eq ↝
 -/
#print linear_map.proj_std_basis_same /- _inst_8: decidable_eq ↝
 -/
#print linear_map.proj_std_basis_ne /- _inst_8: decidable_eq ↝
 -/
#print linear_map.supr_range_std_basis_le_infi_ker_proj /- _inst_8: decidable_eq ↝
 -/
#print linear_map.infi_ker_proj_le_supr_range_std_basis /- _inst_8: decidable_eq ↝
 -/
#print linear_map.supr_range_std_basis_eq_infi_ker_proj /- _inst_8: decidable_eq ↝
 -/
#print linear_map.supr_range_std_basis /- _inst_8: decidable_eq ↝
 -/
#print linear_map.disjoint_std_basis_std_basis /- _inst_8: decidable_eq ↝
 -/
#print linear_map.std_basis_eq_single /- _inst_8: decidable_eq ↝
 -/
#print linear_map.fun_left /- _inst_3: semimodule ↝
 -/
#print linear_map.fun_left_apply /- _inst_3: semimodule ↝
 -/
#print linear_map.fun_left_id /- _inst_3: semimodule ↝
 -/
#print linear_map.fun_left_comp /- _inst_3: semimodule ↝
 -/
#print linear_map.fun_congr_left /- _inst_3: semimodule ↝
 -/
#print linear_map.fun_congr_left_apply /- _inst_3: semimodule ↝
 -/
#print linear_map.fun_congr_left_id /- _inst_3: semimodule ↝
 -/
#print linear_map.fun_congr_left_comp /- _inst_3: semimodule ↝
 -/
#print linear_map.fun_congr_left_symm /- _inst_3: semimodule ↝
 -/
#print linear_map.automorphism_group /- _inst_3: semimodule ↝
 -/
#print linear_map.automorphism_group.to_linear_map_is_monoid_hom /- _inst_3: semimodule ↝
 -/
#print linear_map.general_linear_group /- _inst_3: semimodule ↝
 -/
#print linear_map.general_linear_group.has_coe_to_fun /- _inst_3: semimodule ↝
 -/
#print linear_map.general_linear_group.to_linear_equiv /- _inst_3: semimodule ↝
 -/
#print linear_map.general_linear_group.of_linear_equiv /- _inst_3: semimodule ↝
 -/
#print linear_map.general_linear_group.general_linear_equiv /- _inst_3: semimodule ↝
 -/
#print linear_map.general_linear_group.general_linear_equiv_to_linear_map /- _inst_3: semimodule ↝
 -/

-- linear_algebra\basis.lean
#print is_basis.repr /- _inst_5: module ↝
 -/
#print is_basis.repr_range /- _inst_5: module ↝
 -/
#print is_basis.repr_eq_single /- _inst_5: module ↝
 -/
#print is_basis.range_repr_self /- _inst_5: module ↝
 -/
#print constr_basis /- _inst_6: module ↝
 -/
#print constr_smul /- _inst_8: comm_ring ↝ ring
_inst_10: module ↝
 -/
#print module_equiv_finsupp /- _inst_5: module ↝
 -/
#print module_equiv_finsupp_apply_basis /- _inst_5: module ↝
 -/
#print is_basis_span /- _inst_5: module ↝
 -/
#print is_basis_empty_bot /- _inst_5: module ↝
 -/
#print submodule.exists_is_compl /- _inst_4: vector_space ↝
 -/
#print quotient_prod_linear_equiv /- _inst_4: vector_space ↝
 -/

-- linear_algebra\bilinear_form.lean
#print bilin_form.has_coe_to_fun /- _inst_3: semimodule ↝
 -/
#print bilin_form.coe_fn_mk /- _inst_3: semimodule ↝
 -/
#print bilin_form.coe_fn_congr /- _inst_3: semimodule ↝
 -/
#print bilin_form.add_left /- _inst_3: semimodule ↝
 -/
#print bilin_form.smul_left /- _inst_3: semimodule ↝
 -/
#print bilin_form.add_right /- _inst_3: semimodule ↝
 -/
#print bilin_form.smul_right /- _inst_3: semimodule ↝
 -/
#print bilin_form.zero_left /- _inst_3: semimodule ↝
 -/
#print bilin_form.zero_right /- _inst_3: semimodule ↝
 -/
#print bilin_form.ext /- _inst_3: semimodule ↝
 -/
#print bilin_form.add_comm_monoid /- _inst_3: semimodule ↝
 -/
#print bilin_form.add_apply /- _inst_3: semimodule ↝
 -/
#print bilin_form.inhabited /- _inst_3: semimodule ↝
 -/
#print bilin_form.semimodule /- _inst_14: semimodule ↝
 -/
#print bilin_form.smul_apply /- _inst_13: comm_semiring ↝ semiring
_inst_14: semimodule ↝
 -/
#print linear_map.to_bilin_aux /- _inst_9: semimodule ↝
 -/
#print linear_map.to_bilin /- _inst_9: semimodule ↝
 -/
#print bilin_form.to_lin /- _inst_9: semimodule ↝
 -/
#print linear_map.to_bilin_aux_eq /- _inst_9: semimodule ↝
 -/
#print linear_map.to_bilin_symm /- _inst_9: semimodule ↝
 -/
#print bilin_form.to_lin_symm /- _inst_9: semimodule ↝
 -/
#print to_linear_map_apply /- _inst_9: semimodule ↝
 -/
#print map_sum_left /- _inst_9: semimodule ↝
 -/
#print map_sum_right /- _inst_9: semimodule ↝
 -/
#print bilin_form.comp /- _inst_3: semimodule ↝
_inst_14: semimodule ↝
 -/
#print bilin_form.comp_left /- _inst_3: semimodule ↝
 -/
#print bilin_form.comp_right /- _inst_3: semimodule ↝
 -/
#print bilin_form.comp_left_comp_right /- _inst_3: semimodule ↝
 -/
#print bilin_form.comp_right_comp_left /- _inst_3: semimodule ↝
 -/
#print bilin_form.comp_apply /- _inst_3: semimodule ↝
_inst_14: semimodule ↝
 -/
#print bilin_form.comp_left_apply /- _inst_3: semimodule ↝
 -/
#print bilin_form.comp_right_apply /- _inst_3: semimodule ↝
 -/
#print bilin_form.comp_injective /- _inst_3: semimodule ↝
_inst_14: semimodule ↝
 -/
#print bilin_form.lin_mul_lin /- _inst_9: semimodule ↝
 -/
#print bilin_form.lin_mul_lin_apply /- _inst_9: semimodule ↝
 -/
#print bilin_form.lin_mul_lin_comp /- _inst_9: semimodule ↝
_inst_14: semimodule ↝
 -/
#print bilin_form.lin_mul_lin_comp_left /- _inst_9: semimodule ↝
 -/
#print bilin_form.lin_mul_lin_comp_right /- _inst_9: semimodule ↝
 -/
#print bilin_form.is_ortho /- _inst_3: semimodule ↝
 -/
#print bilin_form.ortho_zero /- _inst_3: semimodule ↝
 -/
#print bilin_form.is_ortho_smul_left /- _inst_13: domain ↝ ring no_zero_divisors
 -/
#print bilin_form.is_ortho_smul_right /- _inst_13: domain ↝ ring no_zero_divisors
 -/
#print bilin_form.to_matrixₗ /- _inst_15: decidable_eq ↝
 -/
#print bilin_form.to_matrix /- _inst_15: decidable_eq ↝
 -/
#print bilin_form.to_matrix_apply /- _inst_15: decidable_eq ↝
 -/
#print bilin_form.to_matrix_smul /- _inst_15: decidable_eq ↝
 -/
#print bilin_form.to_matrix_comp /- _inst_15: decidable_eq ↝
_inst_16: decidable_eq ↝
 -/
#print bilin_form.to_matrix_comp_left /- _inst_15: decidable_eq ↝
 -/
#print bilin_form.to_matrix_comp_right /- _inst_15: decidable_eq ↝
 -/
#print bilin_form.mul_to_matrix_mul /- _inst_15: decidable_eq ↝
_inst_16: decidable_eq ↝
 -/
#print bilin_form.mul_to_matrix /- _inst_15: decidable_eq ↝
 -/
#print bilin_form.to_matrix_mul /- _inst_15: decidable_eq ↝
 -/
#print to_matrix_to_bilin_form /- _inst_15: decidable_eq ↝
 -/
#print to_bilin_form_to_matrix /- _inst_15: decidable_eq ↝
 -/
#print bilin_form_equiv_matrix /- _inst_15: decidable_eq ↝
 -/
#print matrix.to_bilin_form_comp /- _inst_19: decidable_eq ↝
 -/
#print refl_bilin_form.is_refl /- _inst_3: semimodule ↝
 -/
#print refl_bilin_form.eq_zero /- _inst_3: semimodule ↝
 -/
#print refl_bilin_form.ortho_sym /- _inst_3: semimodule ↝
 -/
#print sym_bilin_form.is_sym /- _inst_3: semimodule ↝
 -/
#print sym_bilin_form.sym /- _inst_3: semimodule ↝
 -/
#print sym_bilin_form.is_refl /- _inst_3: semimodule ↝
 -/
#print sym_bilin_form.ortho_sym /- _inst_3: semimodule ↝
 -/
#print alt_bilin_form.is_alt /- _inst_3: semimodule ↝
 -/
#print alt_bilin_form.self_eq_zero /- _inst_3: semimodule ↝
 -/
#print bilin_form.is_adjoint_pair /- _inst_3: semimodule ↝
_inst_14: semimodule ↝
 -/
#print bilin_form.is_adjoint_pair.eq /- _inst_3: semimodule ↝
_inst_14: semimodule ↝
 -/
#print bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right /- _inst_3: semimodule ↝
 -/
#print bilin_form.is_adjoint_pair_zero /- _inst_3: semimodule ↝
_inst_14: semimodule ↝
 -/
#print bilin_form.is_adjoint_pair_id /- _inst_3: semimodule ↝
 -/
#print bilin_form.is_adjoint_pair.add /- _inst_3: semimodule ↝
_inst_14: semimodule ↝
 -/
#print bilin_form.is_adjoint_pair.smul /- _inst_7: comm_semiring ↝ semiring
_inst_9: semimodule ↝
_inst_18: semimodule ↝
 -/
#print bilin_form.is_adjoint_pair.comp /- _inst_3: semimodule ↝
_inst_14: semimodule ↝
_inst_20: semimodule ↝
 -/
#print bilin_form.is_adjoint_pair.mul /- _inst_3: semimodule ↝
 -/
#print bilin_form.is_pair_self_adjoint /- _inst_3: semimodule ↝
 -/
#print bilin_form.is_pair_self_adjoint_submodule /- _inst_9: semimodule ↝
 -/
#print bilin_form.mem_is_pair_self_adjoint_submodule /- _inst_9: semimodule ↝
 -/
#print bilin_form.is_pair_self_adjoint_equiv /- _inst_12: module ↝
_inst_22: module ↝
 -/
#print bilin_form.is_self_adjoint /- _inst_3: semimodule ↝
 -/
#print bilin_form.self_adjoint_submodule /- _inst_9: semimodule ↝
 -/
#print bilin_form.mem_self_adjoint_submodule /- _inst_9: semimodule ↝
 -/
#print bilin_form.skew_adjoint_submodule /- _inst_12: module ↝
 -/
#print bilin_form.mem_skew_adjoint_submodule /- _inst_12: module ↝
 -/
#print matrix.is_adjoint_pair /- _inst_10: comm_ring ↝ add_comm_monoid has_mul
 -/
#print matrix_is_adjoint_pair_bilin_form /- _inst_14: decidable_eq ↝
 -/
#print matrix.is_adjoint_pair_equiv /- _inst_14: decidable_eq ↝
 -/
#print pair_self_adjoint_matrices_submodule /- _inst_14: decidable_eq ↝
 -/
#print mem_pair_self_adjoint_matrices_submodule /- _inst_14: decidable_eq ↝
 -/
#print self_adjoint_matrices_submodule /- _inst_14: decidable_eq ↝
 -/
#print mem_self_adjoint_matrices_submodule /- _inst_14: decidable_eq ↝
 -/
#print skew_adjoint_matrices_submodule /- _inst_14: decidable_eq ↝
 -/
#print mem_skew_adjoint_matrices_submodule /- _inst_14: decidable_eq ↝
 -/

-- linear_algebra\char_poly\basic.lean
#print char_matrix /- _inst_1: comm_ring ↝ ring
_inst_2: decidable_eq ↝
 -/
#print char_matrix_apply_eq /- _inst_2: decidable_eq ↝
 -/
#print char_matrix_apply_ne /- _inst_2: decidable_eq ↝
 -/
#print mat_poly_equiv_char_matrix /- _inst_2: decidable_eq ↝
 -/
#print char_poly /- _inst_2: decidable_eq ↝
 -/
#print aeval_self_char_poly /- _inst_2: decidable_eq ↝
 -/

-- linear_algebra\char_poly\coeff.lean
#print char_matrix_apply_nat_degree /- _inst_2: decidable_eq ↝
 -/
#print char_matrix_apply_nat_degree_le /- _inst_2: decidable_eq ↝
 -/
#print char_poly_sub_diagonal_degree_lt /- _inst_2: decidable_eq ↝
 -/
#print char_poly_coeff_eq_prod_coeff_of_le /- _inst_2: decidable_eq ↝
 -/
#print det_of_card_zero /- _inst_2: decidable_eq ↝
 -/
#print char_poly_degree_eq_dim /- _inst_2: decidable_eq ↝
 -/
#print char_poly_nat_degree_eq_dim /- _inst_2: decidable_eq ↝
 -/
#print char_poly_monic /- _inst_2: decidable_eq ↝
 -/
#print trace_eq_neg_char_poly_coeff /- _inst_2: decidable_eq ↝
 -/
#print mat_poly_equiv_eval /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: decidable_eq ↝
 -/
#print eval_det /- _inst_2: decidable_eq ↝
 -/
#print det_eq_sign_char_poly_coeff /- _inst_2: decidable_eq ↝
 -/
#print finite_field.char_poly_pow_card /- _inst_2: decidable_eq ↝
 -/
#print zmod.char_poly_pow_card /- _inst_2: decidable_eq ↝
 -/
#print finite_field.trace_pow_card /- _inst_2: decidable_eq ↝
 -/
#print zmod.trace_pow_card /- _inst_2: decidable_eq ↝
 -/
#print matrix.is_integral /- _inst_2: decidable_eq ↝
 -/
#print matrix.min_poly_dvd_char_poly /- _inst_2: decidable_eq ↝
 -/

-- linear_algebra\clifford_algebra.lean
#print clifford_algebra.ι /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.ι_square_scalar /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.comp_ι_square_scalar /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.lift_symm_apply /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.lift /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.ι_comp_lift /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.lift_ι_apply /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.lift_unique /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.lift_comp_ι /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.hom_ext /- _inst_3: module ↝ algebra
 -/
#print clifford_algebra.as_exterior /- _inst_3: module ↝ algebra
 -/

-- linear_algebra\contraction.lean
#print contract_left /- _inst_4: module ↝
 -/
#print dual_tensor_hom /- _inst_4: module ↝
_inst_5: module ↝
 -/
#print dual_tensor_hom_apply /- _inst_4: module ↝
_inst_5: module ↝
 -/

-- linear_algebra\determinant.lean
#print matrix.det /- _inst_1: decidable_eq ↝
_inst_3: comm_ring ↝ add_comm_monoid comm_monoid has_neg
 -/
#print matrix.det_diagonal /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_zero /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_one /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_eq_one_of_card_eq_zero /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_mul_aux /- _inst_1: decidable_eq ↝
_inst_3: comm_ring ↝ comm_monoid ring
 -/
#print matrix.det_mul /- _inst_1: decidable_eq ↝
 -/
#print matrix.det.is_monoid_hom /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_transpose /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_permutation /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_permute /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_smul /- _inst_1: decidable_eq ↝
 -/
#print matrix.ring_hom.map_det /- _inst_1: decidable_eq ↝
 -/
#print matrix.alg_hom.map_det /- _inst_1: decidable_eq ↝
_inst_3: comm_ring ↝ comm_semiring
 -/
#print matrix.det_eq_zero_of_row_eq_zero /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_eq_zero_of_column_eq_zero /- _inst_1: decidable_eq ↝
 -/
#print matrix.mod_swap /- _inst_4: decidable_eq ↝
 -/
#print matrix.r.decidable_rel /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_zero_of_row_eq /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_update_column_add /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_update_row_add /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_update_column_smul /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_update_row_smul /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_block_diagonal /- _inst_1: decidable_eq ↝
_inst_5: decidable_eq ↝
 -/

-- linear_algebra\dfinsupp.lean
#print dfinsupp.lmk /- dec_ι: decidable_eq ↝
 -/
#print dfinsupp.lsingle /- dec_ι: decidable_eq ↝
 -/
#print dfinsupp.lhom_ext /- dec_ι: decidable_eq ↝
_inst_5: semimodule ↝
 -/
#print dfinsupp.lhom_ext' /- dec_ι: decidable_eq ↝
_inst_5: semimodule ↝
 -/
#print dfinsupp.lmk_apply /- dec_ι: decidable_eq ↝
 -/
#print dfinsupp.lsingle_apply /- dec_ι: decidable_eq ↝
 -/
#print dfinsupp.lsum_apply /- dec_ι: decidable_eq ↝
_inst_5: semimodule ↝
 -/
#print dfinsupp.lsum /- dec_ι: decidable_eq ↝
_inst_5: semimodule ↝
 -/
#print dfinsupp.lsum_symm_apply /- dec_ι: decidable_eq ↝
_inst_5: semimodule ↝
 -/

-- linear_algebra\dimension.lean
#print dim_bot /- _inst_3: vector_space ↝
 -/
#print dim_top /- _inst_3: vector_space ↝
 -/
#print dim_span /- _inst_3: vector_space ↝
 -/
#print dim_span_set /- _inst_3: vector_space ↝
 -/
#print dim_span_le /- _inst_3: vector_space ↝
 -/
#print dim_span_of_finset /- _inst_3: vector_space ↝
 -/
#print dim_quotient_add_dim /- _inst_3: vector_space ↝
 -/
#print dim_quotient_le /- _inst_3: vector_space ↝
 -/
#print dim_range_add_dim_ker /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
 -/
#print dim_range_le /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
 -/
#print dim_map_le /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
 -/
#print dim_range_of_surjective /- _inst_7: vector_space ↝
 -/
#print dim_eq_of_surjective /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
 -/
#print dim_le_of_surjective /- _inst_3: vector_space ↝
 -/
#print dim_eq_of_injective /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
 -/
#print dim_submodule_le /- _inst_3: vector_space ↝
 -/
#print dim_le_of_injective /- _inst_5: vector_space ↝
 -/
#print dim_le_of_submodule /- _inst_3: vector_space ↝
 -/
#print linear_independent_le_dim /- _inst_3: vector_space ↝
 -/
#print linear_independent_le_dim' /- _inst_3: vector_space ↝
 -/
#print dim_sup_add_dim_inf_eq /- _inst_3: vector_space ↝
 -/
#print dim_add_le_dim_add_dim /- _inst_3: vector_space ↝
 -/
#print exists_mem_ne_zero_of_dim_pos /- _inst_3: vector_space ↝
 -/
#print rank /- _inst_7: vector_space ↝
 -/
#print rank_le_domain /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
 -/
#print rank_add_le /- _inst_7: vector_space ↝
 -/
#print rank_zero /- _inst_7: vector_space ↝
 -/
#print rank_comp_le2 /- _inst_7: vector_space ↝
_inst_11: vector_space ↝
 -/
#print dim_zero_iff_forall_zero /- _inst_3: vector_space ↝
 -/
#print dim_le_one_iff /- _inst_3: vector_space ↝
 -/
#print dim_submodule_le_one_iff /- _inst_3: vector_space ↝
 -/
#print dim_submodule_le_one_iff' /- _inst_3: vector_space ↝
 -/

-- linear_algebra\direct_sum\finsupp.lean
#print finsupp_lequiv_direct_sum /- _inst_3: module ↝
_inst_6: decidable_eq ↝
 -/
#print finsupp_lequiv_direct_sum_single /- _inst_3: module ↝
_inst_6: decidable_eq ↝
 -/
#print finsupp_lequiv_direct_sum_symm_lof /- _inst_3: module ↝
_inst_6: decidable_eq ↝
 -/
#print finsupp_tensor_finsupp /- _inst_8: module ↝
_inst_10: module ↝
 -/
#print finsupp_tensor_finsupp_single /- _inst_8: module ↝
_inst_10: module ↝
 -/
#print finsupp_tensor_finsupp_symm_single /- _inst_8: module ↝
_inst_10: module ↝
 -/

-- linear_algebra\direct_sum\tensor_product.lean
#print tensor_product.direct_sum /- _inst_2: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/
#print tensor_product.direct_sum_lof_tmul_lof /- _inst_2: decidable_eq ↝
_inst_3: decidable_eq ↝
 -/

-- linear_algebra\direct_sum_module.lean
#print direct_sum.lmk /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.lof /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.single_eq_lof /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.mk_smul /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.of_smul /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.support_smul /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.to_module /- dec_ι: decidable_eq ↝
_inst_5: semimodule ↝
 -/
#print direct_sum.to_module_lof /- dec_ι: decidable_eq ↝
_inst_5: semimodule ↝
 -/
#print direct_sum.to_module.unique /- dec_ι: decidable_eq ↝
_inst_5: semimodule ↝
 -/
#print direct_sum.to_module.ext /- dec_ι: decidable_eq ↝
_inst_5: semimodule ↝
 -/
#print direct_sum.lset_to_set /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.lid /- _inst_7: semimodule ↝
 -/
#print direct_sum.lof_apply /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.component.lof_self /- dec_ι: decidable_eq ↝
 -/
#print direct_sum.component.of /- dec_ι: decidable_eq ↝
 -/

-- linear_algebra\dual.lean
#print module.dual /- _inst_1: comm_ring ↝ ring
 -/
#print module.dual.eval_apply /- _inst_3: module ↝
 -/
#print module.dual.transpose /- _inst_3: module ↝
_inst_5: module ↝
 -/
#print module.dual.transpose_apply /- _inst_3: module ↝
_inst_5: module ↝
 -/
#print module.dual.transpose_comp /- _inst_3: module ↝
_inst_5: module ↝
_inst_7: module ↝
 -/
#print is_basis.to_dual /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_apply /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_total_left /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_total_right /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_apply_left /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_apply_right /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_flip /- _inst_3: vector_space ↝
de: decidable_eq ↝
 -/
#print is_basis.to_dual_swap_eq_to_dual /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_eq_repr /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_eq_equiv_fun /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_inj /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_ker /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_range /- de: decidable_eq ↝
 -/
#print is_basis.dual_basis /- de: decidable_eq ↝
 -/
#print is_basis.dual_lin_independent /- de: decidable_eq ↝
 -/
#print is_basis.dual_basis_apply_self /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_equiv /- de: decidable_eq ↝
 -/
#print is_basis.dual_basis_is_basis /- de: decidable_eq ↝
 -/
#print is_basis.total_dual_basis /- de: decidable_eq ↝
 -/
#print is_basis.dual_basis_repr /- de: decidable_eq ↝
 -/
#print is_basis.dual_basis_equiv_fun /- de: decidable_eq ↝
 -/
#print is_basis.dual_basis_apply /- de: decidable_eq ↝
 -/
#print is_basis.to_dual_to_dual /- de: decidable_eq ↝
 -/
#print dual_pair.coeffs /- dι: decidable_eq ↝
 -/
#print dual_pair.coeffs_apply /- dι: decidable_eq ↝
 -/
#print dual_pair.lc /- _inst_3: vector_space ↝ has_scalar
 -/
#print dual_pair.dual_lc /- dι: decidable_eq ↝
 -/
#print dual_pair.coeffs_lc /- dι: decidable_eq ↝
 -/
#print dual_pair.decomposition /- dι: decidable_eq ↝
 -/
#print dual_pair.mem_of_mem_span /- dι: decidable_eq ↝
 -/
#print dual_pair.is_basis /- dι: decidable_eq ↝
 -/
#print dual_pair.eq_dual /- dι: decidable_eq ↝
 -/

-- linear_algebra\eigenspace.lean
#print module.End.eigenspace /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_3: module ↝ algebra
 -/
#print module.End.mem_eigenspace_iff /- _inst_3: module ↝ algebra
 -/
#print module.End.eigenspace_div /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.eigenspace_aeval_polynomial_degree_1 /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.ker_aeval_ring_hom'_unit_polynomial /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.aeval_apply_of_has_eigenvector /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.is_integral /- _inst_6: vector_space ↝ algebra finite_dimensional
 -/
#print module.End.is_root_of_has_eigenvalue /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.has_eigenvalue_of_is_root /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.has_eigenvalue_iff_is_root /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.exists_eigenvalue /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.eigenvectors_linear_independent /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.generalized_eigenspace /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_3: module ↝ algebra
 -/
#print module.End.generalized_eigenrange /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_3: module ↝ algebra
 -/
#print module.End.generalized_eigenspace_mono /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.has_generalized_eigenvalue_of_has_eigenvalue /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.generalized_eigenspace_le_generalized_eigenspace_findim /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.generalized_eigenspace_eq_generalized_eigenspace_findim_of_le /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.generalized_eigenspace_restrict /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.generalized_eigenvec_disjoint_range_ker /- _inst_6: vector_space ↝ algebra
 -/
#print module.End.pos_findim_generalized_eigenspace_of_has_eigenvalue /- _inst_6: vector_space ↝
 -/
#print module.End.map_generalized_eigenrange_le /- _inst_6: vector_space ↝ algebra
 -/
#print linear_map.is_integral /- _inst_3: vector_space ↝ algebra
 -/

-- linear_algebra\exterior_algebra.lean
#print exterior_algebra /- _inst_3: semimodule ↝
 -/
#print exterior_algebra.ring /- _inst_5: semimodule ↝
 -/
#print exterior_algebra.ι /- _inst_3: semimodule ↝ algebra
 -/
#print exterior_algebra.ι_square_zero /- _inst_3: semimodule ↝ algebra
 -/
#print exterior_algebra.comp_ι_square_zero /- _inst_3: semimodule ↝ algebra
 -/
#print exterior_algebra.lift_symm_apply /- _inst_3: semimodule ↝ algebra
 -/
#print exterior_algebra.lift /- _inst_3: semimodule ↝ algebra
 -/
#print exterior_algebra.ι_comp_lift /- _inst_3: semimodule ↝ algebra
 -/
#print exterior_algebra.lift_ι_apply /- _inst_3: semimodule ↝ algebra
 -/
#print exterior_algebra.lift_unique /- _inst_3: semimodule ↝ algebra
 -/
#print exterior_algebra.lift_comp_ι /- _inst_3: semimodule ↝ algebra
 -/
#print exterior_algebra.hom_ext /- _inst_3: semimodule ↝ algebra
 -/

-- linear_algebra\finite_dimensional.lean
#print finite_dimensional.finite_dimensional_iff_dim_lt_omega /- _inst_3: vector_space ↝
 -/
#print finite_dimensional.iff_fg /- _inst_3: vector_space ↝
 -/
#print finite_dimensional.finite_dimensional_submodule /- _inst_3: vector_space ↝
 -/
#print finite_dimensional.finite_dimensional_quotient /- _inst_3: vector_space ↝
 -/
#print finite_dimensional.exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card /- _inst_3: vector_space ↝
 -/
#print finite_dimensional.exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card /- _inst_6: linear_ordered_field ↝ field linear_ordered_cancel_add_comm_monoid
 -/
#print finite_dimensional.eq_top_of_findim_eq /- _inst_3: vector_space ↝ finite_dimensional
 -/
#print finite_dimensional.span_of_finite /- _inst_3: vector_space ↝
 -/
#print finite_dimensional.submodule.span.finite_dimensional /- _inst_3: vector_space ↝
 -/
#print finite_dimensional_bot /- _inst_3: vector_space ↝
 -/
#print findim_bot /- _inst_3: vector_space ↝
 -/
#print bot_eq_top_of_dim_eq_zero /- _inst_3: vector_space ↝
 -/
#print dim_eq_zero /- _inst_3: vector_space ↝
 -/
#print findim_eq_zero /- _inst_3: vector_space ↝
 -/
#print submodule.fg_iff_finite_dimensional /- _inst_3: vector_space ↝
 -/
#print submodule.finite_dimensional_of_le /- _inst_3: vector_space ↝
 -/
#print submodule.finite_dimensional_inf_left /- _inst_3: vector_space ↝
 -/
#print submodule.finite_dimensional_inf_right /- _inst_3: vector_space ↝
 -/
#print submodule.finite_dimensional_sup /- _inst_3: vector_space ↝
 -/
#print submodule.findim_quotient_add_findim /- _inst_3: vector_space ↝ finite_dimensional
 -/
#print submodule.findim_le /- _inst_3: vector_space ↝
 -/
#print submodule.findim_lt /- _inst_3: vector_space ↝ finite_dimensional
 -/
#print submodule.findim_quotient_le /- _inst_3: vector_space ↝
 -/
#print submodule.dim_sup_add_dim_inf_eq /- _inst_3: vector_space ↝ finite_dimensional
 -/
#print submodule.eq_top_of_disjoint /- _inst_3: vector_space ↝ finite_dimensional
 -/
#print finite_dimensional.eq_of_le_of_findim_le /- _inst_3: vector_space ↝
 -/
#print finite_dimensional.eq_of_le_of_findim_eq /- _inst_3: vector_space ↝
 -/
#print linear_map.surjective_of_injective /- _inst_3: vector_space ↝ finite_dimensional
 -/
#print linear_map.finite_dimensional_range /- _inst_3: vector_space ↝ finite_dimensional
_inst_5: vector_space ↝
 -/
#print linear_map.findim_range_add_findim_ker /- _inst_3: vector_space ↝ finite_dimensional
_inst_5: vector_space ↝
 -/
#print linear_equiv.of_injective_endo /- _inst_3: vector_space ↝
 -/
#print findim_top /- _inst_3: vector_space ↝
 -/
#print linear_map.injective_iff_surjective_of_findim_eq_findim /- _inst_3: vector_space ↝ finite_dimensional
_inst_5: vector_space ↝
 -/
#print linear_map.findim_le_findim_of_injective /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
 -/
#print alg_hom.bijective /- _inst_7: field ↝ division_ring
 -/
#print submodule.findim_mono /- _inst_3: vector_space ↝ finite_dimensional
 -/
#print submodule.lt_of_le_of_findim_lt_findim /- _inst_3: vector_space ↝
 -/
#print submodule.lt_top_of_findim_lt_findim /- _inst_3: vector_space ↝
 -/
#print submodule.findim_lt_findim_of_lt /- _inst_3: vector_space ↝ finite_dimensional
 -/
#print findim_span_le_card /- _inst_3: vector_space ↝
 -/
#print findim_span_eq_card /- _inst_3: vector_space ↝
 -/
#print findim_span_set_eq_card /- _inst_3: vector_space ↝
 -/
#print span_lt_of_subset_of_card_lt_findim /- _inst_3: vector_space ↝
 -/
#print span_lt_top_of_card_lt_findim /- _inst_3: vector_space ↝
 -/
#print linear_independent_of_span_eq_top_of_card_eq_findim /- _inst_3: vector_space ↝
 -/
#print linear_independent_iff_card_eq_findim_span /- _inst_3: vector_space ↝
 -/
#print span_eq_top_of_linear_independent_of_card_eq_findim /- _inst_3: vector_space ↝
 -/
#print subalgebra.dim_eq_one_of_eq_bot /- _inst_7: field ↝ nontrivial semiring add_comm_group
 -/
#print subalgebra_top_dim_eq_submodule_top_dim /- _inst_7: field ↝ semiring add_comm_group
 -/
#print subalgebra_top_findim_eq_submodule_top_findim /- _inst_7: field ↝ semiring add_comm_group
 -/
#print subalgebra.eq_bot_of_findim_one /- _inst_7: field ↝ nontrivial ring
 -/
#print module.End.exists_ker_pow_eq_ker_pow_succ /- _inst_3: vector_space ↝
 -/

-- linear_algebra\finsupp.lean
#print finsupp.lsingle /- _inst_3: semimodule ↝
 -/
#print finsupp.lhom_ext /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print finsupp.lhom_ext' /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print finsupp.lapply /- _inst_3: semimodule ↝
 -/
#print finsupp.lsubtype_domain /- _inst_3: semimodule ↝
 -/
#print finsupp.lsubtype_domain_apply /- _inst_3: semimodule ↝
 -/
#print finsupp.lsingle_apply /- _inst_3: semimodule ↝
 -/
#print finsupp.lapply_apply /- _inst_3: semimodule ↝
 -/
#print finsupp.ker_lsingle /- _inst_3: semimodule ↝
 -/
#print finsupp.lsingle_range_le_ker_lapply /- _inst_3: semimodule ↝
 -/
#print finsupp.infi_ker_lapply_le_bot /- _inst_3: semimodule ↝
 -/
#print finsupp.supr_lsingle_range /- _inst_3: semimodule ↝
 -/
#print finsupp.disjoint_lsingle_lsingle /- _inst_3: semimodule ↝
 -/
#print finsupp.span_single_image /- _inst_3: semimodule ↝
 -/
#print finsupp.supported /- _inst_3: semimodule ↝
 -/
#print finsupp.mem_supported /- _inst_3: semimodule ↝
 -/
#print finsupp.mem_supported' /- _inst_3: semimodule ↝
 -/
#print finsupp.single_mem_supported /- _inst_3: semimodule ↝
 -/
#print finsupp.restrict_dom /- _inst_3: semimodule ↝
 -/
#print finsupp.restrict_dom_apply /- _inst_3: semimodule ↝
 -/
#print finsupp.restrict_dom_comp_subtype /- _inst_3: semimodule ↝
 -/
#print finsupp.range_restrict_dom /- _inst_3: semimodule ↝
 -/
#print finsupp.supported_mono /- _inst_3: semimodule ↝
 -/
#print finsupp.supported_empty /- _inst_3: semimodule ↝
 -/
#print finsupp.supported_univ /- _inst_3: semimodule ↝
 -/
#print finsupp.supported_Union /- _inst_3: semimodule ↝
 -/
#print finsupp.supported_union /- _inst_3: semimodule ↝
 -/
#print finsupp.supported_Inter /- _inst_3: semimodule ↝
 -/
#print finsupp.supported_inter /- _inst_3: semimodule ↝
 -/
#print finsupp.disjoint_supported_supported /- _inst_3: semimodule ↝
 -/
#print finsupp.disjoint_supported_supported_iff /- _inst_3: semimodule ↝
 -/
#print finsupp.supported_equiv_finsupp /- _inst_3: semimodule ↝
 -/
#print finsupp.lsum /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print finsupp.coe_lsum /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print finsupp.lsum_apply /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print finsupp.lsum_single /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print finsupp.lsum_symm_apply /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print finsupp.lmap_domain /- _inst_3: semimodule ↝
 -/
#print finsupp.lmap_domain_apply /- _inst_3: semimodule ↝
 -/
#print finsupp.lmap_domain_id /- _inst_3: semimodule ↝
 -/
#print finsupp.lmap_domain_comp /- _inst_3: semimodule ↝
 -/
#print finsupp.supported_comap_lmap_domain /- _inst_3: semimodule ↝
 -/
#print finsupp.lmap_domain_supported /- _inst_3: semimodule ↝
 -/
#print finsupp.lmap_domain_disjoint_ker /- _inst_3: semimodule ↝
 -/
#print finsupp.total /- _inst_3: semimodule ↝
 -/
#print finsupp.total_apply /- _inst_3: semimodule ↝
 -/
#print finsupp.total_apply_of_mem_supported /- _inst_3: semimodule ↝
 -/
#print finsupp.total_single /- _inst_3: semimodule ↝
 -/
#print finsupp.total_unique /- _inst_3: semimodule ↝
 -/
#print finsupp.total_range /- _inst_3: semimodule ↝
 -/
#print finsupp.range_total /- _inst_3: semimodule ↝
 -/
#print finsupp.lmap_domain_total /- _inst_3: semimodule ↝
_inst_7: semimodule ↝
 -/
#print finsupp.total_emb_domain /- _inst_7: semimodule ↝
 -/
#print finsupp.total_map_domain /- _inst_7: semimodule ↝
 -/
#print finsupp.span_eq_map_total /- _inst_3: semimodule ↝
 -/
#print finsupp.mem_span_iff_total /- _inst_3: semimodule ↝
 -/
#print finsupp.total_on /- _inst_3: semimodule ↝
 -/
#print finsupp.total_on_range /- _inst_3: semimodule ↝
 -/
#print finsupp.total_comp /- _inst_3: semimodule ↝
 -/
#print finsupp.total_comap_domain /- _inst_3: semimodule ↝
 -/
#print finsupp.total_on_finset /- _inst_3: semimodule ↝
 -/
#print finsupp.dom_lcongr /- _inst_3: semimodule ↝
 -/
#print finsupp.dom_lcongr_single /- _inst_3: semimodule ↝
 -/
#print finsupp.congr /- _inst_3: semimodule ↝
 -/
#print finsupp.lcongr /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print finsupp.lcongr_single /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print linear_map.map_finsupp_total /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print submodule.exists_finset_of_mem_supr /- _inst_3: semimodule ↝
 -/
#print mem_span_finset /- _inst_3: semimodule ↝
 -/

-- linear_algebra\finsupp_vector_space.lean
#print finsupp.linear_independent_single /- _inst_3: module ↝
 -/
#print finsupp.is_basis_single /- _inst_3: module ↝
 -/
#print finsupp.is_basis.tensor_product /- _inst_3: module ↝
_inst_5: module ↝
 -/
#print finsupp.dim_eq /- _inst_3: vector_space ↝
 -/
#print eq_bot_iff_dim_eq_zero /- _inst_3: vector_space ↝
 -/
#print injective_of_surjective /- _inst_5: vector_space ↝
 -/

-- linear_algebra\lagrange.lean
#print lagrange.basis /- _inst_1: decidable_eq ↝
_inst_2: field ↝ has_inv ring comm_semiring
 -/
#print lagrange.basis_empty /- _inst_1: decidable_eq ↝
 -/
#print lagrange.eval_basis_self /- _inst_1: decidable_eq ↝
 -/
#print lagrange.eval_basis_ne /- _inst_1: decidable_eq ↝
 -/
#print lagrange.eval_basis /- _inst_1: decidable_eq ↝
 -/
#print lagrange.nat_degree_basis /- _inst_1: decidable_eq ↝
 -/
#print lagrange.interpolate /- _inst_1: decidable_eq ↝
 -/
#print lagrange.interpolate_empty /- _inst_1: decidable_eq ↝
 -/
#print lagrange.eval_interpolate /- _inst_1: decidable_eq ↝
 -/
#print lagrange.degree_interpolate_lt /- _inst_1: decidable_eq ↝
 -/
#print lagrange.linterpolate /- _inst_1: decidable_eq ↝
 -/
#print lagrange.interpolate_add /- _inst_1: decidable_eq ↝
 -/
#print lagrange.interpolate_zero /- _inst_1: decidable_eq ↝
 -/
#print lagrange.interpolate_neg /- _inst_1: decidable_eq ↝
 -/
#print lagrange.interpolate_sub /- _inst_1: decidable_eq ↝
 -/
#print lagrange.interpolate_smul /- _inst_1: decidable_eq ↝
 -/
#print lagrange.eq_zero_of_eval_eq_zero /- _inst_3: field ↝ integral_domain
 -/
#print lagrange.eq_interpolate /- _inst_1: decidable_eq ↝
 -/
#print lagrange.fun_equiv_degree_lt /- _inst_1: decidable_eq ↝
 -/

-- linear_algebra\linear_independent.lean
#print linear_independent_iff'' /- _inst_5: module ↝
 -/
#print linear_independent.ne_zero /- _inst_5: module ↝
 -/
#print linear_independent.injective /- _inst_5: module ↝
 -/
#print linear_independent_span /- _inst_5: module ↝
 -/
#print linear_independent_iff_total_on /- _inst_5: module ↝
 -/
#print linear_independent.total_equiv /- _inst_5: module ↝
 -/
#print linear_independent.repr /- _inst_5: module ↝
 -/
#print linear_independent.total_repr /- _inst_5: module ↝
 -/
#print linear_independent.total_comp_repr /- _inst_5: module ↝
 -/
#print linear_independent.repr_ker /- _inst_5: module ↝
 -/
#print linear_independent.repr_range /- _inst_5: module ↝
 -/
#print linear_independent.repr_eq /- _inst_5: module ↝
 -/
#print linear_independent.repr_eq_single /- _inst_5: module ↝
 -/
#print surjective_of_linear_independent_of_span /- _inst_5: module ↝
 -/
#print linear_independent_monoid_hom /- _inst_9: integral_domain ↝ comm_semigroup ring no_zero_divisors
 -/
#print mem_span_insert_exchange /- _inst_4: vector_space ↝
 -/
#print linear_independent_iff_not_mem_span /- _inst_4: vector_space ↝
 -/

-- linear_algebra\linear_pmap.lean
#print linear_pmap.has_coe_to_fun /- _inst_3: module ↝
 -/
#print linear_pmap.to_fun_eq_coe /- _inst_3: module ↝
 -/
#print linear_pmap.map_zero /- _inst_3: module ↝
 -/
#print linear_pmap.map_add /- _inst_3: module ↝
 -/
#print linear_pmap.map_neg /- _inst_3: module ↝
 -/
#print linear_pmap.map_sub /- _inst_3: module ↝
 -/
#print linear_pmap.map_smul /- _inst_3: module ↝
 -/
#print linear_pmap.mk_apply /- _inst_3: module ↝
 -/
#print linear_pmap.mk_span_singleton' /- _inst_3: module ↝
 -/
#print linear_pmap.has_neg /- _inst_3: module ↝
 -/
#print linear_pmap.eq_of_le_of_domain_eq /- _inst_3: module ↝
 -/
#print linear_pmap.has_inf /- _inst_3: module ↝
 -/
#print linear_pmap.has_bot /- _inst_3: module ↝
 -/
#print linear_pmap.sup /- _inst_3: module ↝
 -/
#print linear_pmap.sup_apply /- _inst_3: module ↝
 -/
#print linear_pmap.Sup /- _inst_3: module ↝
 -/
#print linear_pmap.le_Sup /- _inst_3: module ↝
 -/
#print linear_map.to_pmap /- _inst_3: module ↝
 -/
#print linear_map.comp_pmap /- _inst_3: module ↝
 -/
#print linear_pmap.cod_restrict /- _inst_3: module ↝
_inst_5: module ↝
 -/
#print linear_pmap.comp /- _inst_5: module ↝
 -/

-- linear_algebra\matrix.lean
#print matrix.fintype /- _inst_5: decidable_eq ↝
_inst_6: decidable_eq ↝
 -/
#print matrix.mul_vec_std_basis /- _inst_5: decidable_eq ↝
 -/
#print linear_map.to_matrix' /- _inst_5: decidable_eq ↝
 -/
#print matrix.to_lin' /- _inst_5: decidable_eq ↝
 -/
#print linear_map.to_matrix'_symm /- _inst_5: decidable_eq ↝
 -/
#print matrix.to_lin'_symm /- _inst_5: decidable_eq ↝
 -/
#print linear_map.to_matrix'_to_lin' /- _inst_5: decidable_eq ↝
 -/
#print matrix.to_lin'_to_matrix' /- _inst_5: decidable_eq ↝
 -/
#print linear_map.to_matrix'_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix.to_lin'_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix.to_lin'_one /- _inst_5: decidable_eq ↝
 -/
#print linear_map.to_matrix'_id /- _inst_5: decidable_eq ↝
 -/
#print matrix.to_lin'_mul /- _inst_5: decidable_eq ↝
_inst_6: decidable_eq ↝
 -/
#print linear_map.to_matrix'_comp /- _inst_5: decidable_eq ↝
_inst_6: decidable_eq ↝
 -/
#print linear_map.to_matrix'_mul /- _inst_6: decidable_eq ↝
 -/
#print linear_map.to_matrix /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print matrix.to_lin /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print linear_map.to_matrix_symm /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print matrix.to_lin_symm /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print matrix.to_lin_to_matrix /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print linear_map.to_matrix_to_lin /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print linear_map.to_matrix_apply /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print linear_map.to_matrix_apply' /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print matrix.to_lin_apply /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print matrix.to_lin_self /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print linear_map.to_matrix_id /- _inst_5: decidable_eq ↝
_inst_8: module ↝
 -/
#print matrix.to_lin_one /- _inst_5: decidable_eq ↝
_inst_8: module ↝
 -/
#print linear_map.to_matrix_range /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
_inst_10: decidable_eq ↝
_inst_11: decidable_eq ↝
 -/
#print linear_map.to_matrix_comp /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
_inst_11: module ↝
_inst_12: decidable_eq ↝
 -/
#print linear_map.to_matrix_mul /- _inst_5: decidable_eq ↝
_inst_8: module ↝
 -/
#print matrix.to_lin_mul /- _inst_5: decidable_eq ↝
_inst_8: module ↝
_inst_9: module ↝
_inst_11: module ↝
_inst_12: decidable_eq ↝
 -/
#print is_basis.to_matrix /- _inst_3: comm_ring ↝ ring
 -/
#print is_basis.to_matrix_eq_to_matrix_constr /- _inst_5: module ↝
_inst_6: decidable_eq ↝
 -/
#print is_basis.to_matrix_self /- _inst_6: decidable_eq ↝
 -/
#print is_basis.to_matrix_update /- _inst_6: decidable_eq ↝
 -/
#print is_basis.to_lin_to_matrix /- _inst_5: module ↝
_inst_6: decidable_eq ↝
 -/
#print is_basis_to_matrix_mul_linear_map_to_matrix /- _inst_5: module ↝
_inst_7: module ↝
_inst_8: decidable_eq ↝
 -/
#print linear_map_to_matrix_mul_is_basis_to_matrix /- _inst_5: module ↝
_inst_7: module ↝
_inst_8: decidable_eq ↝
_inst_9: decidable_eq ↝
 -/
#print linear_equiv.is_unit_det /- _inst_3: module ↝
_inst_5: module ↝
_inst_6: decidable_eq ↝
 -/
#print linear_equiv.of_is_unit_det /- _inst_3: module ↝
_inst_5: module ↝
_inst_6: decidable_eq ↝
 -/
#print is_basis.det /- _inst_6: decidable_eq ↝
 -/
#print is_basis.det_apply /- _inst_6: decidable_eq ↝
 -/
#print is_basis.det_self /- _inst_6: decidable_eq ↝
 -/
#print is_basis.iff_det /- _inst_3: module ↝
_inst_6: decidable_eq ↝
 -/
#print linear_map.to_matrix_transpose /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
_inst_8: decidable_eq ↝
_inst_9: decidable_eq ↝
 -/
#print linear_map.to_matrix_symm_transpose /- _inst_3: vector_space ↝
_inst_5: vector_space ↝
_inst_8: decidable_eq ↝
_inst_9: decidable_eq ↝
 -/
#print matrix.diag /- _inst_5: semimodule ↝
 -/
#print matrix.diag_apply /- _inst_5: semimodule ↝
 -/
#print matrix.diag_one /- _inst_6: decidable_eq ↝
 -/
#print matrix.diag_transpose /- _inst_5: semimodule ↝
 -/
#print matrix.trace /- _inst_5: semimodule ↝
 -/
#print matrix.trace_diag /- _inst_5: semimodule ↝
 -/
#print matrix.trace_one /- _inst_6: decidable_eq ↝
 -/
#print matrix.trace_transpose /- _inst_5: semimodule ↝
 -/
#print matrix.trace_mul_comm /- _inst_6: comm_ring ↝ comm_semiring
 -/
#print matrix.proj_diagonal /- _inst_2: decidable_eq ↝
 -/
#print matrix.diagonal_comp_std_basis /- _inst_2: decidable_eq ↝
 -/
#print matrix.diagonal_to_lin' /- _inst_2: decidable_eq ↝
 -/
#print matrix.to_linear_equiv /- _inst_2: decidable_eq ↝
 -/
#print matrix.to_linear_equiv_apply /- _inst_2: decidable_eq ↝
 -/
#print matrix.to_linear_equiv_symm_apply /- _inst_2: decidable_eq ↝
 -/
#print matrix.rank_vec_mul_vec /- _inst_6: decidable_eq ↝
 -/
#print matrix.ker_diagonal_to_lin' /- _inst_4: decidable_eq ↝
 -/
#print matrix.range_diagonal /- _inst_4: decidable_eq ↝
 -/
#print matrix.rank_diagonal /- _inst_4: decidable_eq ↝
_inst_5: decidable_eq ↝
 -/
#print matrix.reindex_alg_equiv /- _inst_8: decidable_eq ↝
_inst_9: decidable_eq ↝
 -/
#print matrix.reindex_alg_equiv_apply /- _inst_8: decidable_eq ↝
_inst_9: decidable_eq ↝
 -/
#print matrix.reindex_alg_equiv_symm_apply /- _inst_8: decidable_eq ↝
_inst_9: decidable_eq ↝
 -/
#print matrix.det_reindex_self' /- _inst_7: decidable_eq ↝
_inst_8: decidable_eq ↝
 -/
#print matrix.det_reindex_self /- _inst_7: decidable_eq ↝
_inst_8: decidable_eq ↝
 -/
#print matrix.det_reindex_linear_equiv_self /- _inst_7: decidable_eq ↝
_inst_8: decidable_eq ↝
 -/
#print matrix.det_reindex_alg_equiv /- _inst_7: decidable_eq ↝
_inst_8: decidable_eq ↝
 -/
#print linear_map.trace_aux /- _inst_3: module ↝
_inst_4: decidable_eq ↝
 -/
#print linear_map.trace_aux_def /- _inst_3: module ↝
_inst_4: decidable_eq ↝
 -/
#print linear_map.trace_aux_eq' /- _inst_3: module ↝
_inst_4: decidable_eq ↝
_inst_6: decidable_eq ↝
 -/
#print linear_map.trace_aux_range /- _inst_3: module ↝
_inst_4: decidable_eq ↝
 -/
#print linear_map.trace_aux_eq /- _inst_3: module ↝
_inst_4: decidable_eq ↝
_inst_6: decidable_eq ↝
 -/
#print linear_map.trace /- _inst_3: module ↝
 -/
#print linear_map.trace_eq_matrix_trace /- _inst_3: module ↝
_inst_5: decidable_eq ↝
 -/
#print linear_map.trace_mul_comm /- _inst_3: module ↝
 -/
#print linear_map.finite_dimensional /- _inst_3: vector_space ↝
_inst_6: vector_space ↝
 -/
#print linear_map.findim_linear_map /- _inst_3: vector_space ↝ finite_dimensional
_inst_6: vector_space ↝ finite_dimensional
 -/
#print alg_equiv_matrix' /- _inst_3: decidable_eq ↝
 -/
#print linear_equiv.alg_conj /- _inst_3: module ↝ algebra
_inst_5: module ↝ algebra
 -/
#print alg_equiv_matrix /- _inst_4: module ↝ algebra
_inst_5: decidable_eq ↝
 -/

-- linear_algebra\multilinear.lean
#print multilinear_map.has_coe_to_fun /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.ext /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.map_add /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.map_smul /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.map_coord_zero /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.map_zero /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.has_add /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.add_apply /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.has_zero /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.inhabited /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.zero_apply /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.add_comm_monoid /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.sum_apply /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.to_linear_map /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.prod /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print multilinear_map.restr /- _inst_10: semimodule ↝
_inst_12: semimodule ↝
 -/
#print multilinear_map.cons_add /- _inst_10: semimodule ↝
 -/
#print multilinear_map.cons_smul /- _inst_10: semimodule ↝
 -/
#print multilinear_map.snoc_add /- _inst_10: semimodule ↝
 -/
#print multilinear_map.snoc_smul /- _inst_10: semimodule ↝
 -/
#print multilinear_map.comp_linear_map /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.comp_linear_map_apply /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.map_piecewise_add /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.map_add_univ /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.map_sum_finset_aux /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.map_sum_finset /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.map_sum /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
 -/
#print multilinear_map.restrict_scalars /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
_inst_16: semimodule ↝
_inst_18: is_scalar_tower ↝
 -/
#print multilinear_map.coe_restrict_scalars /- _inst_1: decidable_eq ↝
_inst_10: semimodule ↝
_inst_16: semimodule ↝
_inst_18: is_scalar_tower ↝
 -/
#print linear_map.comp_multilinear_map /- _inst_1: decidable_eq ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.coe_comp_multilinear_map /- _inst_1: decidable_eq ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.comp_multilinear_map_apply /- _inst_1: decidable_eq ↝
_inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print multilinear_map.map_piecewise_smul /- _inst_1: decidable_eq ↝
_inst_2: comm_semiring ↝ comm_monoid semiring
_inst_8: semimodule ↝
 -/
#print multilinear_map.map_smul_univ /- _inst_1: decidable_eq ↝
_inst_8: semimodule ↝
 -/
#print multilinear_map.has_scalar /- _inst_1: decidable_eq ↝
_inst_13: semimodule ↝
_inst_14: semimodule ↝
_inst_15: is_scalar_tower ↝
 -/
#print multilinear_map.smul_apply /- _inst_1: decidable_eq ↝
_inst_11: algebra ↝ has_scalar
_inst_13: semimodule ↝ has_scalar
_inst_14: semimodule ↝
_inst_15: is_scalar_tower ↝ has_scalar
 -/
#print multilinear_map.semimodule /- _inst_1: decidable_eq ↝
_inst_13: semimodule ↝
_inst_14: semimodule ↝
_inst_15: is_scalar_tower ↝
 -/
#print multilinear_map.mk_pi_algebra /- _inst_1: decidable_eq ↝
 -/
#print multilinear_map.mk_pi_algebra_apply /- _inst_1: decidable_eq ↝
 -/
#print multilinear_map.smul_right /- _inst_1: decidable_eq ↝
_inst_2: comm_semiring ↝ semiring
_inst_8: semimodule ↝
 -/
#print multilinear_map.smul_right_apply /- _inst_1: decidable_eq ↝
_inst_8: semimodule ↝
 -/
#print multilinear_map.mk_pi_ring /- _inst_1: decidable_eq ↝
_inst_8: semimodule ↝
 -/
#print multilinear_map.mk_pi_ring_apply /- _inst_1: decidable_eq ↝
_inst_8: semimodule ↝
 -/
#print multilinear_map.mk_pi_ring_apply_one_eq_self /- _inst_1: decidable_eq ↝
_inst_8: semimodule ↝
 -/
#print multilinear_map.map_sub /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print multilinear_map.has_neg /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print multilinear_map.neg_apply /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print multilinear_map.add_comm_group /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print multilinear_map.pi_ring_equiv /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print linear_map.uncurry_left_apply /- _inst_8: module ↝
 -/
#print linear_map.curry_uncurry_left /- _inst_8: module ↝
 -/
#print multilinear_map.uncurry_curry_left /- _inst_8: module ↝
 -/
#print multilinear_map.uncurry_right_apply /- _inst_8: module ↝
 -/
#print multilinear_map.curry_uncurry_right /- _inst_8: module ↝
 -/
#print multilinear_map.uncurry_curry_right /- _inst_8: module ↝
 -/

-- linear_algebra\nonsingular_inverse.lean
#print matrix.cramer_map /- _inst_1: decidable_eq ↝
 -/
#print matrix.cramer_map_is_linear /- _inst_1: decidable_eq ↝
 -/
#print matrix.cramer_is_linear /- _inst_1: decidable_eq ↝
 -/
#print matrix.cramer /- _inst_1: decidable_eq ↝
 -/
#print matrix.cramer_apply /- _inst_1: decidable_eq ↝
 -/
#print matrix.cramer_transpose_row_self /- _inst_1: decidable_eq ↝
 -/
#print matrix.sum_cramer /- _inst_1: decidable_eq ↝
 -/
#print matrix.sum_cramer_apply /- _inst_1: decidable_eq ↝
 -/
#print matrix.adjugate /- _inst_1: decidable_eq ↝
 -/
#print matrix.adjugate_def /- _inst_1: decidable_eq ↝
 -/
#print matrix.adjugate_apply /- _inst_1: decidable_eq ↝
 -/
#print matrix.adjugate_transpose /- _inst_1: decidable_eq ↝
 -/
#print matrix.cramer_eq_adjugate_mul_vec /- _inst_1: decidable_eq ↝
 -/
#print matrix.mul_adjugate_apply /- _inst_1: decidable_eq ↝
 -/
#print matrix.mul_adjugate /- _inst_1: decidable_eq ↝
 -/
#print matrix.adjugate_mul /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_adjugate_of_cancel /- _inst_1: decidable_eq ↝
 -/
#print matrix.adjugate_eq_one_of_card_eq_one /- _inst_1: decidable_eq ↝
 -/
#print matrix.adjugate_zero /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_adjugate_eq_one /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_adjugate_of_is_unit /- _inst_1: decidable_eq ↝
 -/
#print matrix.is_unit_det_transpose /- _inst_1: decidable_eq ↝
 -/
#print matrix.nonsing_inv /- _inst_1: decidable_eq ↝
 -/
#print matrix.has_inv /- _inst_1: decidable_eq ↝
 -/
#print matrix.nonsing_inv_apply /- _inst_1: decidable_eq ↝
 -/
#print matrix.transpose_nonsing_inv /- _inst_1: decidable_eq ↝
 -/
#print matrix.mul_nonsing_inv /- _inst_1: decidable_eq ↝
 -/
#print matrix.nonsing_inv_mul /- _inst_1: decidable_eq ↝
 -/
#print matrix.nonsing_inv_det /- _inst_1: decidable_eq ↝
 -/
#print matrix.is_unit_nonsing_inv_det /- _inst_1: decidable_eq ↝
 -/
#print matrix.nonsing_inv_nonsing_inv /- _inst_1: decidable_eq ↝
 -/
#print matrix.nonsing_inv_unit /- _inst_1: decidable_eq ↝
 -/
#print matrix.is_unit_iff_is_unit_det /- _inst_1: decidable_eq ↝
 -/
#print matrix.is_unit_det_of_left_inverse /- _inst_1: decidable_eq ↝
 -/
#print matrix.is_unit_det_of_right_inverse /- _inst_1: decidable_eq ↝
 -/
#print matrix.nonsing_inv_left_right /- _inst_1: decidable_eq ↝
 -/
#print matrix.nonsing_inv_right_left /- _inst_1: decidable_eq ↝
 -/
#print matrix.det_smul_inv_mul_vec_eq_cramer /- _inst_1: decidable_eq ↝
 -/
#print matrix.mul_vec_cramer /- _inst_1: decidable_eq ↝
 -/

-- linear_algebra\projection.lean
#print linear_map.ker_id_sub_eq_of_proj /- _inst_3: module ↝
 -/
#print linear_map.range_eq_of_proj /- _inst_3: module ↝
 -/
#print linear_map.is_compl_of_proj /- _inst_3: module ↝
 -/
#print submodule.quotient_equiv_of_is_compl /- _inst_3: module ↝
 -/
#print submodule.quotient_equiv_of_is_compl_symm_apply /- _inst_3: module ↝
 -/
#print submodule.quotient_equiv_of_is_compl_apply_mk_coe /- _inst_3: module ↝
 -/
#print submodule.mk_quotient_equiv_of_is_compl_apply /- _inst_3: module ↝
 -/
#print submodule.prod_equiv_of_is_compl /- _inst_3: module ↝
 -/
#print submodule.coe_prod_equiv_of_is_compl /- _inst_3: module ↝
 -/
#print submodule.coe_prod_equiv_of_is_compl' /- _inst_3: module ↝
 -/
#print submodule.prod_equiv_of_is_compl_symm_apply_left /- _inst_3: module ↝
 -/
#print submodule.prod_equiv_of_is_compl_symm_apply_right /- _inst_3: module ↝
 -/
#print submodule.prod_equiv_of_is_compl_symm_apply_fst_eq_zero /- _inst_3: module ↝
 -/
#print submodule.prod_equiv_of_is_compl_symm_apply_snd_eq_zero /- _inst_3: module ↝
 -/
#print submodule.linear_proj_of_is_compl /- _inst_3: module ↝
 -/
#print submodule.linear_proj_of_is_compl_apply_left /- _inst_3: module ↝
 -/
#print submodule.linear_proj_of_is_compl_range /- _inst_3: module ↝
 -/
#print submodule.linear_proj_of_is_compl_apply_eq_zero_iff /- _inst_3: module ↝
 -/
#print submodule.linear_proj_of_is_compl_apply_right' /- _inst_3: module ↝
 -/
#print submodule.linear_proj_of_is_compl_apply_right /- _inst_3: module ↝
 -/
#print submodule.linear_proj_of_is_compl_ker /- _inst_3: module ↝
 -/
#print submodule.linear_proj_of_is_compl_comp_subtype /- _inst_3: module ↝
 -/
#print submodule.linear_proj_of_is_compl_idempotent /- _inst_3: module ↝
 -/
#print linear_map.linear_proj_of_is_compl_of_proj /- _inst_3: module ↝
 -/
#print submodule.is_compl_equiv_proj /- _inst_3: module ↝
 -/
#print submodule.coe_is_compl_equiv_proj_apply /- _inst_3: module ↝
 -/
#print submodule.coe_is_compl_equiv_proj_symm_apply /- _inst_3: module ↝
 -/

-- linear_algebra\quadratic_form.lean
#print quadratic_form.polar /- _inst_1: add_comm_group ↝ has_add
_inst_2: ring ↝ has_sub
 -/
#print quadratic_form.polar_comm /- _inst_3: comm_ring ↝ ring
 -/
#print quadratic_form.map_add_self /- _inst_4: module ↝
 -/
#print quadratic_form.coe_fn_smul /- _inst_3: comm_ring ↝ ring
 -/
#print quadratic_form.smul_apply /- _inst_3: comm_ring ↝ ring
 -/
#print quadratic_form.associated /- _inst_5: module ↝
 -/
#print quadratic_form.associated_apply /- _inst_5: module ↝
 -/
#print quadratic_form.associated_is_sym /- _inst_5: module ↝
 -/
#print quadratic_form.associated_comp /- _inst_5: module ↝
_inst_8: module ↝
 -/
#print quadratic_form.associated_lin_mul_lin /- _inst_5: module ↝
 -/
#print quadratic_form.associated_to_quadratic_form /- _inst_5: module ↝
 -/
#print quadratic_form.associated_left_inverse /- _inst_5: module ↝
 -/
#print quadratic_form.associated_right_inverse /- _inst_5: module ↝
 -/
#print quadratic_form.pos_def /- _inst_6: ordered_ring ↝ has_lt ring
 -/
#print quadratic_form.pos_def.smul /- _inst_8: linear_ordered_comm_ring ↝ ordered_ring
 -/
#print quadratic_form.lin_mul_lin_self_pos_def /- _inst_8: linear_ordered_comm_ring ↝ linear_ordered_ring comm_ring
 -/
#print matrix.to_quadratic_form /- _inst_3: comm_ring ↝ ring comm_semiring
 -/
#print quadratic_form.to_matrix /- _inst_7: decidable_eq ↝
 -/
#print quadratic_form.to_matrix_smul /- _inst_7: decidable_eq ↝
 -/
#print quadratic_form.to_matrix_comp /- _inst_7: decidable_eq ↝
_inst_9: decidable_eq ↝
 -/
#print quadratic_form.discr /- _inst_7: decidable_eq ↝
 -/
#print quadratic_form.discr_smul /- _inst_7: decidable_eq ↝
 -/
#print quadratic_form.discr_comp /- _inst_7: decidable_eq ↝
 -/

-- linear_algebra\sesquilinear_form.lean
#print sesq_form.ortho_smul_left /- _inst_1: domain ↝ ring no_zero_divisors
 -/
#print sesq_form.ortho_smul_right /- _inst_1: domain ↝ ring no_zero_divisors
 -/

-- linear_algebra\special_linear_group.lean
#print matrix.special_linear_group /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.coe_matrix /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.coe_fun /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.to_lin' /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.ext_iff /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.ext /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.has_inv /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.has_mul /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.has_one /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.inhabited /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.inv_val /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.inv_apply /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.mul_val /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.mul_apply /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.one_val /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.one_apply /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.det_coe_matrix /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.det_coe_fun /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.to_lin'_mul /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.to_lin'_one /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.group /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.to_linear_equiv /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.to_GL /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.coe_to_GL /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.to_GL_one /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.to_GL_mul /- _inst_1: decidable_eq ↝
 -/
#print matrix.special_linear_group.embedding_GL /- _inst_1: decidable_eq ↝
 -/

-- linear_algebra\tensor_algebra.lean
#print tensor_algebra /- _inst_3: semimodule ↝
 -/
#print tensor_algebra.ring /- _inst_5: semimodule ↝
 -/
#print tensor_algebra.ι /- _inst_3: semimodule ↝ algebra
 -/
#print tensor_algebra.ring_quot_mk_alg_hom_free_algebra_ι_eq_ι /- _inst_3: semimodule ↝ algebra
 -/
#print tensor_algebra.lift /- _inst_3: semimodule ↝ algebra
 -/
#print tensor_algebra.lift_symm_apply /- _inst_3: semimodule ↝ algebra
 -/
#print tensor_algebra.ι_comp_lift /- _inst_3: semimodule ↝ algebra
 -/
#print tensor_algebra.lift_ι_apply /- _inst_3: semimodule ↝ algebra
 -/
#print tensor_algebra.lift_unique /- _inst_3: semimodule ↝ algebra
 -/
#print tensor_algebra.lift_comp_ι /- _inst_3: semimodule ↝ algebra
 -/
#print tensor_algebra.hom_ext /- _inst_3: semimodule ↝ algebra
 -/

-- linear_algebra\tensor_product.lean
#print linear_map.mk₂ /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.mk₂_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.ext₂ /- _inst_1: comm_semiring ↝ semiring
_inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.flip /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.flip_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.flip_inj /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.lflip /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.lflip_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.map_zero₂ /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.map_neg₂ /- _inst_12: comm_ring ↝ ring comm_semiring
_inst_16: module ↝
_inst_17: module ↝
_inst_18: module ↝
 -/
#print linear_map.map_add₂ /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.map_smul₂ /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.lcomp /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.lcomp_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.llcomp /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.llcomp_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.compl₂ /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print linear_map.compl₂_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print linear_map.compr₂ /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print linear_map.compr₂_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print linear_map.lsmul /- _inst_7: semimodule ↝
 -/
#print linear_map.lsmul_apply /- _inst_7: semimodule ↝
 -/
#print tensor_product /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.add_comm_monoid /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.inhabited /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.induction_on /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.zero_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.add_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.tmul_zero /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.tmul_add /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.smul_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.smul.aux /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.smul.aux_of /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.has_scalar /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.smul_zero /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.smul_add /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.smul_tmul' /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.semimodule /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.tmul_smul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.mk /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.mk_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.ite_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.tmul_ite /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.sum_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.tmul_sum /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.lift_aux /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lift_aux_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lift_aux.smul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lift /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lift.tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lift.tmul' /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.ext /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lift.unique /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lift_mk /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.lift_compr₂ /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print tensor_product.lift_mk_compr₂ /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.mk_compr₂_inj /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.uncurry /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.uncurry_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lift.equiv /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lcurry /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.lcurry_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.curry /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.curry_apply /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.ext_threefold /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print tensor_product.ext_fourfold /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print tensor_product.lid /- _inst_7: semimodule ↝
 -/
#print tensor_product.lid_tmul /- _inst_7: semimodule ↝
 -/
#print tensor_product.lid_symm_apply /- _inst_7: semimodule ↝
 -/
#print tensor_product.comm /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.comm_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.comm_symm_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print tensor_product.rid /- _inst_7: semimodule ↝
 -/
#print tensor_product.rid_tmul /- _inst_7: semimodule ↝
 -/
#print tensor_product.rid_symm_apply /- _inst_7: semimodule ↝
 -/
#print tensor_product.assoc /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.assoc_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.assoc_symm_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print tensor_product.map /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print tensor_product.map_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print tensor_product.map_comp /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_13: semimodule ↝
_inst_15: semimodule ↝
 -/
#print tensor_product.lift_comp_map /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_15: semimodule ↝
 -/
#print tensor_product.congr /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print tensor_product.congr_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print tensor_product.congr_symm_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print linear_map.ltensor /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.rtensor /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.ltensor_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.rtensor_tmul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.ltensor_hom /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.rtensor_hom /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.coe_ltensor_hom /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.coe_rtensor_hom /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.ltensor_add /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.rtensor_add /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.ltensor_zero /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.rtensor_zero /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.ltensor_smul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.rtensor_smul /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
 -/
#print linear_map.ltensor_comp /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print linear_map.rtensor_comp /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print linear_map.ltensor_id /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.rtensor_id /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
 -/
#print linear_map.ltensor_comp_rtensor /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print linear_map.rtensor_comp_ltensor /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
 -/
#print linear_map.map_comp_rtensor /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print linear_map.map_comp_ltensor /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print linear_map.rtensor_comp_map /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print linear_map.ltensor_comp_map /- _inst_7: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print tensor_product.add_comm_group /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_7: module ↝
_inst_8: module ↝
 -/
#print tensor_product.neg_tmul /- _inst_7: module ↝
_inst_8: module ↝
 -/
#print tensor_product.tmul_neg /- _inst_7: module ↝
_inst_8: module ↝
 -/
#print linear_map.ltensor_sub /- _inst_7: module ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print linear_map.rtensor_sub /- _inst_7: module ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print linear_map.ltensor_neg /- _inst_7: module ↝
_inst_8: module ↝
_inst_9: module ↝
 -/
#print linear_map.rtensor_neg /- _inst_7: module ↝
_inst_8: module ↝
_inst_9: module ↝
 -/

-- logic\basic.lean
#print coe_coe /- _inst_1: has_coe ↝ has_lift_t
_inst_2: has_coe_t ↝ has_lift_t
 -/
#print coe_fn_coe_trans /- _inst_1: has_coe ↝ has_lift_t has_coe_to_fun
_inst_2: has_coe_t_aux ↝ has_coe_to_fun
 -/
#print coe_fn_coe_base /- _inst_1: has_coe ↝ has_lift_t has_coe_to_fun
 -/
#print coe_sort_coe_trans /- _inst_1: has_coe ↝ has_lift_t has_coe_to_sort
_inst_2: has_coe_t_aux ↝ has_coe_to_sort
 -/
#print coe_sort_coe_base /- _inst_1: has_coe ↝ has_lift_t has_coe_to_sort
 -/

-- logic\function\basic.lean
#print function.injective.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print function.update /- _inst_1: decidable_eq ↝
 -/
#print function.update_same /- _inst_1: decidable_eq ↝
 -/
#print function.update_injective /- _inst_1: decidable_eq ↝
 -/
#print function.update_noteq /- _inst_1: decidable_eq ↝
 -/
#print function.rel_update_iff /- _inst_1: decidable_eq ↝
 -/
#print function.update_eq_iff /- _inst_1: decidable_eq ↝
 -/
#print function.eq_update_iff /- _inst_1: decidable_eq ↝
 -/
#print function.update_eq_self /- _inst_1: decidable_eq ↝
 -/
#print function.update_comp /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print function.apply_update /- _inst_3: decidable_eq ↝
 -/
#print function.comp_update /- _inst_1: decidable_eq ↝
 -/
#print function.update_comm /- _inst_3: decidable_eq ↝
 -/
#print function.update_idem /- _inst_3: decidable_eq ↝
 -/

-- measure_theory\ae_eq_fun.lean
#print measure_theory.ae_eq_fun.has_scalar /- _inst_10: semimodule ↝
 -/
#print measure_theory.ae_eq_fun.smul_mk /- _inst_10: semimodule ↝
 -/
#print measure_theory.ae_eq_fun.coe_fn_smul /- _inst_10: semimodule ↝
 -/
#print measure_theory.ae_eq_fun.smul_to_germ /- _inst_10: semimodule ↝
 -/
#print measure_theory.ae_eq_fun.semimodule /- _inst_10: semimodule ↝
 -/
#print measure_theory.ae_eq_fun.edist_smul /- _inst_8: normed_space ↝
 -/

-- measure_theory\bochner_integration.lean
#print measure_theory.simple_func.integral /- _inst_5: normed_space ↝
 -/
#print measure_theory.simple_func.integral_eq_sum_filter /- _inst_5: normed_space ↝
 -/
#print measure_theory.simple_func.integral_eq_sum_of_subset /- _inst_5: normed_space ↝
 -/
#print measure_theory.simple_func.map_integral /- _inst_5: normed_space ↝
 -/
#print measure_theory.simple_func.integral_congr /- _inst_6: normed_space ↝
 -/
#print measure_theory.simple_func.integral_add /- _inst_6: normed_space ↝
 -/
#print measure_theory.simple_func.integral_neg /- _inst_6: normed_space ↝
 -/
#print measure_theory.simple_func.integral_sub /- _inst_6: normed_space ↝
 -/
#print measure_theory.simple_func.integral_smul /- _inst_6: normed_space ↝
 -/
#print measure_theory.simple_func.norm_integral_le_integral_norm /- _inst_6: normed_space ↝
 -/
#print measure_theory.simple_func.integral_add_measure /- _inst_6: normed_space ↝
 -/
#print measure_theory.l1.simple_func.has_scalar /- _inst_11: normed_space ↝
 -/
#print measure_theory.l1.simple_func.coe_smul /- _inst_11: normed_space ↝
 -/
#print measure_theory.l1.simple_func.semimodule /- _inst_11: normed_space ↝
 -/
#print measure_theory.l1.simple_func.normed_space /- _inst_11: normed_space ↝
 -/
#print measure_theory.l1.simple_func.of_simple_func_smul /- _inst_11: normed_space ↝
 -/
#print measure_theory.l1.simple_func.smul_to_simple_func /- _inst_11: normed_space ↝
 -/
#print measure_theory.l1.simple_func.coe_to_l1 /- _inst_11: normed_space ↝
 -/
#print measure_theory.l1.simple_func.integral /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.simple_func.integral_eq_integral /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.simple_func.integral_congr /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.simple_func.integral_add /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.simple_func.integral_smul /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.simple_func.norm_integral_le_norm /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.simple_func.integral_clm /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.simple_func.norm_Integral_le_one /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.integral_clm /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.integral /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.integral_eq /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.simple_func.integral_l1_eq_integral /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.integral_zero /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.integral_add /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.integral_neg /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.integral_sub /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.integral_smul /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.norm_Integral_le_one /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.norm_integral_le /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.continuous_integral /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_eq /- _inst_4: normed_space ↝
 -/
#print measure_theory.l1.integral_eq_integral /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_undef /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_non_measurable /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_zero /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_zero' /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_add /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_add' /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_neg /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_neg' /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_sub /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_sub' /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_smul /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_congr_ae /- _inst_4: normed_space ↝
 -/
#print measure_theory.l1.integral_of_fun_eq_integral /- _inst_4: normed_space ↝
 -/
#print measure_theory.continuous_integral /- _inst_4: normed_space ↝
 -/
#print measure_theory.norm_integral_le_lintegral_norm /- _inst_4: normed_space ↝
 -/
#print measure_theory.ennnorm_integral_le_lintegral_ennnorm /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_eq_zero_of_ae /- _inst_4: normed_space ↝
 -/
#print measure_theory.tendsto_integral_of_l1 /- _inst_4: normed_space ↝
 -/
#print measure_theory.tendsto_integral_of_dominated_convergence /- _inst_4: normed_space ↝
 -/
#print measure_theory.tendsto_integral_filter_of_dominated_convergence /- _inst_4: normed_space ↝
 -/
#print measure_theory.norm_integral_le_integral_norm /- _inst_4: normed_space ↝
 -/
#print measure_theory.norm_integral_le_of_norm_le /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_finset_sum /- _inst_4: normed_space ↝
 -/
#print measure_theory.simple_func.integral_eq_integral /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_const /- _inst_4: normed_space ↝
 -/
#print measure_theory.norm_integral_le_of_norm_le_const /- _inst_4: normed_space ↝
 -/
#print measure_theory.tendsto_integral_approx_on_univ /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_add_measure /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_add_measure' /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_zero_measure /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_smul_measure /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_map /- _inst_4: normed_space ↝
 -/
#print measure_theory.integral_dirac /- _inst_4: normed_space ↝
 -/

-- measure_theory\borel_space.lean
#print is_measurable.nhds_within_is_measurably_generated /- _inst_3: opens_measurable_space ↝ filter.is_measurably_generated
 -/
#print is_measurable_le' /- _inst_11: partial_order ↝ preorder
 -/
#print measurable_of_continuous_on_compl_singleton /- _inst_11: t1_space ↝ measurable_singleton_class
 -/
#print measurable.smul /- _inst_15: semimodule ↝
 -/
#print measurable.const_smul /- _inst_14: semimodule ↝
 -/
#print measurable_const_smul_iff /- _inst_12: division_ring ↝ group_with_zero semiring
_inst_14: semimodule ↝
 -/
#print measurable.const_mul /- _inst_15: topological_semiring ↝ topological_semimodule
 -/
#print measurable.mul_const /- _inst_15: topological_semiring ↝ has_continuous_mul
 -/
#print measurable_inv' /- _inst_11: normed_field ↝ has_inv t1_space has_zero has_continuous_inv' topological_space opens_measurable_space
 -/
#print measurable_supr /- _inst_11: complete_linear_order ↝ complete_lattice linear_order
 -/
#print measurable_infi /- _inst_11: complete_linear_order ↝ complete_lattice linear_order
 -/
#print measurable_cSup /- _inst_11: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order order_closed_topology
 -/
#print continuous_linear_map.measurable /- _inst_4: normed_space ↝
_inst_8: normed_space ↝
 -/
#print continuous_linear_map.measurable_comp /- _inst_4: normed_space ↝
_inst_8: normed_space ↝
 -/
#print measurable_smul_const /- _inst_7: normed_space ↝
 -/

-- measure_theory\content.lean
#print measure_theory.is_left_invariant_inner_content /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#print measure_theory.outer_measure.is_left_invariant_of_content /- _inst_4: topological_group ↝ has_continuous_mul
 -/

-- measure_theory\group.lean
#print measure_theory.measure.conj /- _inst_2: group ↝ has_inv
 -/

-- measure_theory\haar_measure.lean
#print measure_theory.measure.haar.index /- _inst_1: group ↝ has_mul
 -/

-- measure_theory\integration.lean
#print measure_theory.simple_func.range_map /- _inst_2: decidable_eq ↝
 -/
#print measure_theory.simple_func.semimodule /- _inst_4: semimodule ↝
 -/
#print measure_theory.simple_func.fin_meas_supp.mul /- _inst_4: monoid_with_zero ↝ mul_zero_class
 -/

-- measure_theory\interval_integral.lean
#print interval_integrable /- _inst_1: linear_order ↝ preorder
 -/
#print interval_integrable.smul /- _inst_7: normed_space ↝
 -/
#print interval_integral /- _inst_1: linear_order ↝ preorder
_inst_7: normed_space ↝
 -/
#print interval_integral.integral_zero /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_of_le /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_same /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_symm /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_of_ge /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_cases /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_non_measurable /- _inst_7: normed_space ↝
 -/
#print interval_integral.norm_integral_eq_norm_integral_Ioc /- _inst_7: normed_space ↝
 -/
#print interval_integral.norm_integral_le_integral_norm_Ioc /- _inst_7: normed_space ↝
 -/
#print interval_integral.norm_integral_le_abs_integral_norm /- _inst_7: normed_space ↝
 -/
#print interval_integral.norm_integral_le_of_norm_le_const_ae /- _inst_7: normed_space ↝
 -/
#print interval_integral.norm_integral_le_of_norm_le_const /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_add /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_neg /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_sub /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_smul /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_const' /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_const /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_smul_measure /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_comp_add_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_comp_mul_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_comp_neg /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_add_adjacent_intervals_cancel /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_add_adjacent_intervals /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_interval_sub_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_interval_add_interval_comm /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_interval_sub_interval_comm /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_interval_sub_interval_comm' /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_Iic_sub_Iic /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_const_of_cdf /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_eq_integral_of_support_subset /- _inst_7: normed_space ↝
 -/
#print interval_integral.FTC_filter.nhds /- _inst_12: opens_measurable_space ↝ filter.is_measurably_generated
_inst_13: order_topology ↝ filter.tendsto_Ixx_class
 -/
#print interval_integral.FTC_filter.nhds_univ /- _inst_12: opens_measurable_space ↝ interval_integral.FTC_filter
_inst_13: order_topology ↝ interval_integral.FTC_filter
 -/
#print interval_integral.FTC_filter.nhds_left /- _inst_12: opens_measurable_space ↝ filter.is_measurably_generated
_inst_13: order_topology ↝ filter.tendsto_Ixx_class filter.is_measurably_generated
 -/
#print interval_integral.FTC_filter.nhds_right /- _inst_12: opens_measurable_space ↝ filter.is_measurably_generated
_inst_13: order_topology ↝ filter.tendsto_Ixx_class filter.is_measurably_generated
 -/
#print interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae' /- _inst_7: normed_space ↝
 -/
#print interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' /- _inst_7: normed_space ↝
 -/
#print interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge' /- _inst_7: normed_space ↝
 -/
#print interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae /- _inst_7: normed_space ↝
 -/
#print interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae_of_le /- _inst_7: normed_space ↝
 -/
#print interval_integral.measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge /- _inst_7: normed_space ↝
 -/
#print interval_integral.measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae /- _inst_7: normed_space ↝
_inst_10: order_topology ↝ order_closed_topology
_inst_11: borel_space ↝ opens_measurable_space
 -/
#print interval_integral.measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_sub_linear_is_o_of_tendsto_ae /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_sub_integral_sub_linear_is_o_of_tendsto_ae /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_strict_fderiv_at_of_tendsto_ae /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_strict_fderiv_at /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_strict_deriv_at_of_tendsto_ae_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_strict_deriv_at_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_strict_deriv_at_of_tendsto_ae_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_strict_deriv_at_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_fderiv_at_of_tendsto_ae /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_fderiv_at /- _inst_7: normed_space ↝
 -/
#print interval_integral.fderiv_integral_of_tendsto_ae /- _inst_7: normed_space ↝
 -/
#print interval_integral.fderiv_integral /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_deriv_at_of_tendsto_ae_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_deriv_at_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.deriv_integral_of_tendsto_ae_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.deriv_integral_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_deriv_at_of_tendsto_ae_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_deriv_at_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.deriv_integral_of_tendsto_ae_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.deriv_integral_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_fderiv_within_at_of_tendsto_ae /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_fderiv_within_at /- _inst_7: normed_space ↝
 -/
#print interval_integral.fderiv_within_integral_of_tendsto_ae /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_deriv_within_at_of_tendsto_ae_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_deriv_within_at_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.deriv_within_integral_of_tendsto_ae_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.deriv_within_integral_right /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_deriv_within_at_of_tendsto_ae_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.integral_has_deriv_within_at_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.deriv_within_integral_of_tendsto_ae_left /- _inst_7: normed_space ↝
 -/
#print interval_integral.deriv_within_integral_left /- _inst_7: normed_space ↝
 -/

-- measure_theory\l1_space.lean
#print measure_theory.lintegral_edist_triangle /- _inst_2: normed_group ↝ emetric_space
 -/
#print measure_theory.all_ae_of_real_F_le_bound /- _inst_2: normed_group ↝ has_norm
 -/
#print measure_theory.has_finite_integral.smul /- _inst_5: normed_space ↝
 -/
#print measure_theory.has_finite_integral_smul_iff /- _inst_5: normed_space ↝
 -/
#print measure_theory.integrable.smul /- _inst_8: normed_space ↝
 -/
#print measure_theory.integrable_smul_iff /- _inst_8: normed_space ↝
 -/
#print measure_theory.integrable_smul_const /- _inst_12: normed_space ↝
 -/
#print measure_theory.ae_eq_fun.integrable /- _inst_2: normed_group ↝ emetric_space has_zero
 -/
#print measure_theory.ae_eq_fun.integrable.smul /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.edist_eq /- _inst_8: borel_space ↝ opens_measurable_space
 -/
#print measure_theory.l1.dist_eq /- _inst_8: borel_space ↝ opens_measurable_space
 -/
#print measure_theory.l1.has_scalar /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.coe_smul /- _inst_8: borel_space ↝ has_scalar opens_measurable_space
_inst_10: normed_space ↝ has_scalar
 -/
#print measure_theory.l1.semimodule /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.normed_space /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.of_fun_smul /- _inst_10: normed_space ↝
 -/
#print measure_theory.l1.measurable /- _inst_8: borel_space ↝ opens_measurable_space
 -/
#print measure_theory.l1.integrable /- _inst_8: borel_space ↝ opens_measurable_space
 -/
#print measure_theory.l1.smul_to_fun /- _inst_10: normed_space ↝
 -/

-- measure_theory\prod.lean
#print measurable.integral_prod_right /- _inst_9: normed_space ↝
 -/
#print measurable.integral_prod_right' /- _inst_9: normed_space ↝
 -/
#print measurable.integral_prod_left /- _inst_9: normed_space ↝
 -/
#print measurable.integral_prod_left' /- _inst_9: normed_space ↝
 -/
#print measure_theory.integrable.integral_prod_left /- _inst_10: normed_space ↝
 -/
#print measure_theory.integrable.integral_prod_right /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_prod_swap /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_fn_integral_add /- _inst_10: normed_space ↝
_inst_18: normed_space ↝
 -/
#print measure_theory.integral_fn_integral_sub /- _inst_10: normed_space ↝
_inst_18: normed_space ↝
 -/
#print measure_theory.lintegral_fn_integral_sub /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_integral_add /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_integral_add' /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_integral_sub /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_integral_sub' /- _inst_10: normed_space ↝
 -/
#print measure_theory.continuous_integral_integral /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_prod /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_prod_symm /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_integral /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_integral_symm /- _inst_10: normed_space ↝
 -/
#print measure_theory.integral_integral_swap /- _inst_10: normed_space ↝
 -/

-- measure_theory\set_integral.lean
#print measure_theory.integrable_add /- _inst_6: opens_measurable_space ↝ measurable_singleton_class
 -/
#print measure_theory.integral_union /- _inst_7: normed_space ↝
 -/
#print measure_theory.integral_empty /- _inst_7: normed_space ↝
 -/
#print measure_theory.integral_univ /- _inst_7: normed_space ↝
 -/
#print measure_theory.integral_add_compl /- _inst_7: normed_space ↝
 -/
#print measure_theory.integral_indicator /- _inst_7: normed_space ↝
 -/
#print measure_theory.set_integral_const /- _inst_7: normed_space ↝
 -/
#print measure_theory.integral_indicator_const /- _inst_7: normed_space ↝
 -/
#print measure_theory.set_integral_map /- _inst_7: normed_space ↝
 -/
#print measure_theory.norm_set_integral_le_of_norm_le_const_ae /- _inst_7: normed_space ↝
 -/
#print measure_theory.norm_set_integral_le_of_norm_le_const_ae' /- _inst_7: normed_space ↝
 -/
#print measure_theory.norm_set_integral_le_of_norm_le_const_ae'' /- _inst_7: normed_space ↝
 -/
#print measure_theory.norm_set_integral_le_of_norm_le_const /- _inst_7: normed_space ↝
 -/
#print measure_theory.norm_set_integral_le_of_norm_le_const' /- _inst_7: normed_space ↝
 -/
#print filter.tendsto.integral_sub_linear_is_o_ae /- _inst_4: normed_space ↝
 -/
#print continuous_at.integral_sub_linear_is_o_ae /- _inst_5: opens_measurable_space ↝ filter.is_measurably_generated
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.norm_comp_l1_apply_le /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.integrable_comp /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.comp_l1 /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.comp_l1_apply /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.integrable_comp_l1 /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.measurable_comp_l1 /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.integral_comp_l1 /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.comp_l1ₗ /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.norm_comp_l1_le /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.comp_l1L /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.norm_compl1L_le /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.continuous_integral_comp_l1 /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.integral_comp_comm /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print continuous_linear_map.integral_comp_l1_comm /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print fst_integral /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print snd_integral /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print integral_pair /- _inst_4: normed_space ↝
_inst_6: normed_space ↝
 -/
#print integral_smul_const /- _inst_4: normed_space ↝
 -/

-- measure_theory\simple_func_dense.lean
#print measure_theory.simple_func.integrable_approx_on /- _inst_7: borel_space ↝ opens_measurable_space
 -/

-- number_theory\arithmetic_function.lean
#print nat.arithmetic_function.pmul_comm /- _inst_1: comm_monoid_with_zero ↝ comm_semigroup mul_zero_class
 -/
#print nat.arithmetic_function.pmul_zeta /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print nat.arithmetic_function.zeta_pmul /- _inst_1: monoid_with_zero ↝ monoid mul_zero_class
 -/
#print nat.arithmetic_function.is_multiplicative /- _inst_1: monoid_with_zero ↝ has_one has_zero has_mul
 -/
#print nat.arithmetic_function.is_multiplicative_zeta /- _inst_1: semiring ↝ monoid_with_zero
 -/

-- order\basic.lean
#print order.preimage.decidable /- H: decidable_rel ↝
 -/
#print monotone /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#print le_update_iff /- _inst_2: decidable_eq ↝
 -/
#print update_le_iff /- _inst_2: decidable_eq ↝
 -/
#print as_linear_order.linear_order /- _inst_2: is_total ↝
 -/

-- order\bounded_lattice.lean
#print top_sup_eq /- _inst_1: semilattice_sup_top ↝ order_top semilattice_sup
 -/
#print sup_top_eq /- _inst_1: semilattice_sup_top ↝ order_top semilattice_sup
 -/
#print bot_sup_eq /- _inst_1: semilattice_sup_bot ↝ semilattice_sup order_bot
 -/
#print sup_bot_eq /- _inst_1: semilattice_sup_bot ↝ semilattice_sup order_bot
 -/
#print sup_eq_bot_iff /- _inst_1: semilattice_sup_bot ↝ semilattice_sup order_bot
 -/
#print top_inf_eq /- _inst_1: semilattice_inf_top ↝ semilattice_inf order_top
 -/
#print inf_top_eq /- _inst_1: semilattice_inf_top ↝ semilattice_inf order_top
 -/
#print inf_eq_top_iff /- _inst_1: semilattice_inf_top ↝ semilattice_inf order_top
 -/
#print bot_inf_eq /- _inst_1: semilattice_inf_bot ↝ semilattice_inf order_bot
 -/
#print inf_bot_eq /- _inst_1: semilattice_inf_bot ↝ semilattice_inf order_bot
 -/
#print inf_eq_bot_iff_le_compl /- _inst_1: bounded_distrib_lattice ↝ semilattice_sup_bot distrib_lattice semilattice_inf_top
 -/
#print eq_bot_of_bot_eq_top /- _inst_1: bounded_lattice ↝ order_top order_bot
 -/
#print eq_top_of_bot_eq_top /- _inst_1: bounded_lattice ↝ order_top order_bot
 -/
#print subsingleton_of_top_le_bot /- _inst_1: bounded_lattice ↝ order_top order_bot
 -/
#print with_bot.coe_le /- _inst_1: partial_order ↝ preorder
 -/
#print with_bot.coe_lt_coe /- _inst_1: partial_order ↝ preorder
 -/
#print with_bot.decidable_le /- _inst_2: decidable_rel ↝
 -/
#print with_bot.decidable_lt /- _inst_2: decidable_rel ↝
 -/
#print with_top.coe_le_coe /- _inst_1: partial_order ↝ preorder
 -/
#print with_top.coe_lt_coe /- _inst_1: partial_order ↝ preorder
 -/
#print with_top.coe_lt_top /- _inst_1: partial_order ↝ preorder
 -/
#print with_top.decidable_le /- _inst_2: decidable_rel ↝
 -/
#print with_top.decidable_lt /- _inst_2: decidable_rel ↝
 -/
#print disjoint /- _inst_1: semilattice_inf_bot ↝ has_bot has_le has_inf
 -/
#print disjoint_sup_left /- _inst_1: bounded_distrib_lattice ↝ semilattice_sup_bot distrib_lattice semilattice_inf_bot
 -/
#print disjoint_sup_right /- _inst_1: bounded_distrib_lattice ↝ semilattice_sup_bot distrib_lattice semilattice_inf_bot
 -/
#print is_compl.le_left_iff /- _inst_1: bounded_distrib_lattice ↝ bounded_lattice distrib_lattice
 -/
#print is_compl.sup_inf /- _inst_1: bounded_distrib_lattice ↝ bounded_lattice distrib_lattice
 -/

-- order\bounds.lean
#print upper_bounds /- _inst_1: preorder ↝ has_le
 -/
#print lower_bounds /- _inst_1: preorder ↝ has_le
 -/
#print is_glb.exists_between_self_add /- _inst_1: linear_ordered_add_comm_group ↝ linear_order ordered_cancel_add_comm_monoid
 -/
#print is_lub.exists_between_sub_self /- _inst_1: linear_ordered_add_comm_group ↝ linear_order ordered_add_comm_group
 -/

-- order\complete_boolean_algebra.lean
#print compl_infi /- _inst_1: complete_boolean_algebra ↝ boolean_algebra complete_lattice
 -/

-- order\complete_lattice.lean
#print Inf_lt_iff /- _inst_1: complete_linear_order ↝ complete_lattice linear_order
 -/
#print lt_Sup_iff /- _inst_1: complete_linear_order ↝ complete_lattice linear_order
 -/

-- order\conditionally_complete_lattice.lean
#print exists_lt_of_lt_cSup /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order
 -/
#print exists_lt_of_cInf_lt /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order
 -/
#print cSup_intro' /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice
 -/
#print with_top.is_glb_Inf /- _inst_1: conditionally_complete_linear_order_bot ↝ conditionally_complete_lattice order_bot
 -/
#print with_bot.cSup_empty /- _inst_1: conditionally_complete_lattice ↝ has_Sup
 -/
#print Sup_within_of_ord_connected /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice
 -/
#print Inf_within_of_ord_connected /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice
 -/

-- order\filter\at_top_bot.lean
#print filter.prod_at_top_at_top_eq /- _inst_1: semilattice_sup ↝ preorder
_inst_2: semilattice_sup ↝ preorder
 -/

-- order\filter\basic.lean
#print filter.eventually_eq.div /- _inst_1: group_with_zero ↝ has_inv has_mul has_div
 -/
#print filter.eventually_eq.sub /- _inst_1: add_group ↝ has_sub has_neg has_add
 -/

-- order\filter\extr.lean
#print is_min_filter /- _inst_1: preorder ↝ has_le
 -/
#print is_max_filter /- _inst_1: preorder ↝ has_le
 -/

-- order\filter\filter_product.lean
#print filter.germ.le_def /- _inst_1: preorder ↝ has_le
 -/

-- order\filter\germ.lean
#print filter.germ.mul_action /- _inst_2: mul_action ↝
 -/
#print filter.germ.mul_action' /- _inst_2: mul_action ↝
 -/
#print filter.germ.distrib_mul_action /- _inst_3: distrib_mul_action ↝
 -/
#print filter.germ.distrib_mul_action' /- _inst_3: distrib_mul_action ↝
 -/
#print filter.germ.semimodule /- _inst_3: semimodule ↝
 -/
#print filter.germ.semimodule' /- _inst_3: semimodule ↝
 -/

-- order\filter\interval.lean
#print filter.tendsto_Icc_pure_pure /- _inst_2: partial_order ↝ preorder
 -/
#print filter.tendsto_Ico_pure_bot /- _inst_2: partial_order ↝ preorder
 -/
#print filter.tendsto_Ioc_pure_bot /- _inst_2: partial_order ↝ preorder
 -/
#print filter.tendsto_Ioo_pure_bot /- _inst_2: partial_order ↝ preorder
 -/

-- order\filter\ultrafilter.lean
#print filter.is_ultrafilter_hyperfilter /- _inst_1: infinite ↝ filter.ne_bot
 -/

-- order\fixed_points.lean
#print lfp /- _inst_1: complete_lattice ↝ has_Inf has_le
 -/
#print gfp /- _inst_1: complete_lattice ↝ has_Sup has_le
 -/
#print fixed_points.sup_le_f_of_fixed_points /- _inst_1: complete_lattice ↝ semilattice_sup
 -/
#print fixed_points.f_le_inf_of_fixed_points /- _inst_1: complete_lattice ↝ semilattice_inf
 -/

-- order\galois_connection.lean
#print galois_connection /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#print galois_connection.u_l_u_eq_u /- _inst_2: partial_order ↝ preorder
 -/
#print galois_connection.l_u_l_eq_l /- _inst_1: partial_order ↝ preorder
 -/
#print galois_connection.l_unique /- _inst_1: partial_order ↝ preorder
 -/
#print galois_connection.u_unique /- _inst_2: partial_order ↝ preorder
 -/
#print galois_insertion.strict_mono_u /- _inst_2: partial_order ↝ preorder
 -/

-- order\lattice.lean
#print sup_ind /- _inst_2: is_total ↝
 -/
#print sup_lt_iff /- _inst_2: is_total ↝
 -/
#print le_sup_iff /- _inst_2: is_total ↝
 -/
#print lt_sup_iff /- _inst_2: is_total ↝
 -/
#print inf_ind /- _inst_2: is_total ↝
 -/
#print lt_inf_iff /- _inst_2: is_total ↝
 -/
#print inf_le_iff /- _inst_2: is_total ↝
 -/
#print sup_inf_le /- _inst_1: lattice ↝ semilattice_inf semilattice_sup
 -/
#print le_inf_sup /- _inst_1: lattice ↝ semilattice_inf semilattice_sup
 -/
#print inf_sup_self /- _inst_1: lattice ↝ semilattice_inf semilattice_sup
 -/
#print sup_inf_self /- _inst_1: lattice ↝ semilattice_inf semilattice_sup
 -/
#print monotone.map_sup /- _inst_2: is_total ↝
 -/
#print monotone.map_inf /- _inst_2: is_total ↝
 -/

-- order\lexicographic.lean
#print lex.decidable_eq /- _inst_1: decidable_eq ↝
_inst_2: decidable_eq ↝
 -/
#print lex_has_le /- _inst_1: preorder ↝ has_lt
_inst_2: preorder ↝ has_le
 -/
#print lex_has_lt /- _inst_1: preorder ↝ has_lt
_inst_2: preorder ↝ has_lt
 -/
#print dlex_has_le /- _inst_1: preorder ↝ has_lt
 -/
#print dlex_has_lt /- _inst_1: preorder ↝ has_lt
 -/

-- order\liminf_limsup.lean
#print filter.Limsup /- _inst_1: conditionally_complete_lattice ↝ has_Inf has_le
 -/
#print filter.Liminf /- _inst_1: conditionally_complete_lattice ↝ has_Sup has_le
 -/
#print filter.liminf_le_limsup /- _inst_1: complete_lattice ↝ conditionally_complete_lattice order_top order_bot
 -/

-- order\omega_complete_partial_order.lean
#print complete_lattice.inf_continuous /- _inst_3: is_total ↝
 -/
#print complete_lattice.top_continuous /- _inst_2: complete_lattice ↝ omega_complete_partial_order order_top
 -/
#print complete_lattice.bot_continuous /- _inst_2: complete_lattice ↝ omega_complete_partial_order order_bot
 -/
#print omega_complete_partial_order.continuous_hom.ωSup_bind /- _inst_1: omega_complete_partial_order ↝ preorder
 -/

-- order\rel_classes.lean
#print is_total.swap /- _inst_1: is_total ↝
 -/
#print is_preorder.swap /- _inst_1: is_preorder ↝ is_trans is_refl
 -/
#print is_strict_order.swap /- _inst_1: is_strict_order ↝ is_irrefl is_trans
 -/
#print is_partial_order.swap /- _inst_1: is_partial_order ↝ is_antisymm is_preorder
 -/
#print is_total_preorder.swap /- _inst_1: is_total_preorder ↝ is_preorder
 -/
#print is_linear_order.swap /- _inst_1: is_linear_order ↝ is_partial_order
 -/
#print ge.is_refl /- _inst_1: preorder ↝ has_le is_refl
 -/
#print ge.is_trans /- _inst_1: preorder ↝ has_le is_trans
 -/
#print has_le.le.is_preorder /- _inst_1: preorder ↝ has_le is_trans is_refl
 -/
#print ge.is_preorder /- _inst_1: preorder ↝ has_le is_trans is_refl
 -/
#print gt.is_irrefl /- _inst_1: preorder ↝ has_lt is_irrefl
 -/
#print gt.is_trans /- _inst_1: preorder ↝ has_lt is_trans
 -/
#print gt.is_asymm /- _inst_1: preorder ↝ has_lt is_asymm
 -/
#print has_lt.lt.is_antisymm /- _inst_1: preorder ↝ has_lt is_asymm
 -/
#print gt.is_antisymm /- _inst_1: preorder ↝ has_lt is_asymm
 -/
#print has_lt.lt.is_strict_order /- _inst_1: preorder ↝ has_lt is_irrefl is_trans
 -/
#print gt.is_strict_order /- _inst_1: preorder ↝ has_lt is_irrefl is_trans
 -/
#print preorder.is_total_preorder /- _inst_1: preorder ↝ has_le is_trans
_inst_2: is_total ↝
 -/
#print ge.is_antisymm /- _inst_1: partial_order ↝ is_antisymm has_le
 -/
#print has_le.le.is_partial_order /- _inst_1: partial_order ↝ is_antisymm has_le is_trans is_refl
 -/
#print ge.is_partial_order /- _inst_1: partial_order ↝ is_antisymm has_le is_trans is_refl
 -/
#print ge.is_total /- _inst_1: linear_order ↝ has_le
 -/
#print linear_order.is_total_preorder /- _inst_1: linear_order ↝ has_le
 -/
#print ge.is_total_preorder /- _inst_1: linear_order ↝ has_le
 -/
#print has_le.le.is_linear_order /- _inst_1: linear_order ↝ is_antisymm has_le is_refl
 -/
#print ge.is_linear_order /- _inst_1: linear_order ↝ is_antisymm has_le is_refl
 -/
#print gt.is_trichotomous /- _inst_1: linear_order ↝ is_trichotomous has_lt
 -/
#print order_dual.is_total_le /- _inst_2: is_total ↝
 -/
#print is_strict_total_order'.swap /- _inst_1: is_strict_total_order' ↝ is_trichotomous is_strict_order
 -/
#print has_lt.lt.is_strict_total_order' /- _inst_1: linear_order ↝ is_trichotomous has_lt is_irrefl is_trans
 -/
#print is_order_connected_of_is_strict_total_order' /- _inst_1: is_strict_total_order' ↝ is_trichotomous is_trans
 -/
#print is_strict_total_order_of_is_strict_total_order' /- _inst_1: is_strict_total_order' ↝ is_trichotomous is_asymm is_order_connected
 -/
#print has_lt.lt.is_strict_total_order /- _inst_1: linear_order ↝ has_lt is_strict_total_order'
 -/
#print has_lt.lt.is_order_connected /- _inst_1: linear_order ↝ has_lt is_strict_total_order'
 -/
#print has_lt.lt.is_incomp_trans /- _inst_1: linear_order ↝ has_lt is_strict_weak_order
 -/
#print has_lt.lt.is_strict_weak_order /- _inst_1: linear_order ↝ has_lt is_strict_weak_order
 -/
#print is_extensional_of_is_strict_total_order' /- _inst_1: is_strict_total_order' ↝ is_trichotomous is_irrefl
 -/
#print is_well_order.is_strict_total_order /- _inst_1: is_well_order ↝ is_strict_total_order
 -/
#print is_well_order.is_extensional /- _inst_1: is_well_order ↝ is_extensional
 -/
#print is_well_order.is_trichotomous /- _inst_1: is_well_order ↝ is_trichotomous
 -/
#print is_well_order.is_trans /- _inst_1: is_well_order ↝ is_trans
 -/
#print is_well_order.is_irrefl /- _inst_1: is_well_order ↝ is_irrefl
 -/
#print is_well_order.is_asymm /- _inst_1: is_well_order ↝ is_asymm
 -/
#print is_well_order.linear_order /- _inst_1: is_well_order ↝ is_strict_total_order'
 -/

-- order\rel_iso.lean
#print rel_embedding.is_total /- _inst_1: is_total ↝
 -/
#print rel_embedding.is_preorder /- _inst_1: is_preorder ↝ is_trans is_refl
 -/
#print rel_embedding.is_partial_order /- _inst_1: is_partial_order ↝ is_antisymm is_preorder
 -/
#print rel_embedding.is_linear_order /- _inst_1: is_linear_order ↝ is_partial_order
 -/
#print rel_embedding.is_strict_order /- _inst_1: is_strict_order ↝ is_irrefl is_trans
 -/
#print rel_embedding.is_strict_total_order' /- _inst_1: is_strict_total_order' ↝ is_trichotomous is_strict_order
 -/
#print order_embedding.map_le_iff /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/

-- order\semiconj_Sup.lean
#print is_order_right_adjoint /- _inst_2: preorder ↝ has_le
 -/

-- order\zorn.lean
#print zorn.chain.total /- _inst_1: preorder ↝ has_le is_refl
 -/

-- representation_theory\maschke.lean
#print linear_map.conjugate /- _inst_6: is_scalar_tower ↝
_inst_10: is_scalar_tower ↝
 -/
#print linear_map.conjugate_i /- _inst_6: is_scalar_tower ↝
_inst_10: is_scalar_tower ↝
 -/
#print linear_map.sum_of_conjugates /- _inst_6: is_scalar_tower ↝
_inst_10: is_scalar_tower ↝
 -/
#print linear_map.sum_of_conjugates_equivariant /- _inst_6: is_scalar_tower ↝
_inst_10: is_scalar_tower ↝
 -/
#print linear_map.equivariant_projection /- _inst_4: module ↝
_inst_6: is_scalar_tower ↝
_inst_10: is_scalar_tower ↝
 -/
#print linear_map.equivariant_projection_condition /- _inst_4: module ↝
_inst_6: is_scalar_tower ↝
_inst_10: is_scalar_tower ↝
 -/
#print monoid_algebra.exists_left_inverse_of_injective /- _inst_7: is_scalar_tower ↝
_inst_11: is_scalar_tower ↝
 -/
#print monoid_algebra.submodule.exists_is_compl /- _inst_7: is_scalar_tower ↝
 -/

-- ring_theory\adjoin.lean
#print algebra.adjoin_singleton_eq_range /- _inst_2: comm_semiring ↝ semiring
 -/
#print algebra.adjoin_singleton_one /- _inst_2: comm_semiring ↝ semiring
 -/
#print algebra.adjoin_union_coe_submodule /- _inst_2: comm_semiring ↝ comm_monoid semiring
 -/
#print algebra.adjoin_int /- _inst_1: comm_ring ↝ is_subring ring
 -/
#print algebra.mem_adjoin_iff /- _inst_1: comm_ring ↝ is_subring comm_semiring
 -/
#print algebra.fg_trans /- _inst_1: comm_ring ↝ is_subring comm_semiring
_inst_2: comm_ring ↝ is_subring comm_semiring
 -/

-- ring_theory\adjoin_root.lean
#print adjoin_root.aeval_alg_hom_eq_zero /- _inst_2: comm_ring ↝ comm_semiring
 -/

-- ring_theory\algebra_tower.lean
#print is_scalar_tower.algebra_map_smul /- _inst_6: semimodule ↝
_inst_7: semimodule ↝ has_scalar
_inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.smul_left_comm /- _inst_6: semimodule ↝
_inst_7: semimodule ↝
_inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.algebra_map_eq /- _inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.algebra_map_apply /- _inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.subalgebra' /- _inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.algebra_comap_eq /- _inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.to_alg_hom /- _inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.to_alg_hom_apply /- _inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.restrict_base /- _inst_10: is_scalar_tower ↝
_inst_11: is_scalar_tower ↝
 -/
#print is_scalar_tower.restrict_base_apply /- _inst_10: is_scalar_tower ↝
_inst_11: is_scalar_tower ↝
 -/
#print is_scalar_tower.polynomial /- _inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.aeval_apply /- _inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.invertible.algebra_tower /- _inst_10: is_scalar_tower ↝
 -/
#print is_scalar_tower.algebra_map_aeval /- _inst_7: is_scalar_tower ↝
 -/
#print is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero /- _inst_7: is_scalar_tower ↝
 -/
#print is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero_field /- _inst_9: field ↝ division_ring comm_semiring
_inst_15: is_scalar_tower ↝
 -/
#print is_scalar_tower.linear_map /- _inst_9: comm_semiring ↝ semiring
_inst_11: semimodule ↝
 -/
#print is_scalar_tower.int /- _inst_2: comm_ring ↝ ring comm_semiring
_inst_3: comm_ring ↝ ring
 -/
#print is_scalar_tower.rat /- _inst_1: field ↝ division_ring comm_semiring
 -/
#print algebra.adjoin_algebra_map' /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
_inst_3: comm_ring ↝ semiring
 -/
#print algebra.adjoin_algebra_map /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
_inst_3: comm_ring ↝ semiring
_inst_7: is_scalar_tower ↝
 -/
#print subalgebra.res /- _inst_7: is_scalar_tower ↝
 -/
#print subalgebra.res_top /- _inst_7: is_scalar_tower ↝
 -/
#print subalgebra.mem_res /- _inst_7: is_scalar_tower ↝
 -/
#print subalgebra.res_inj /- _inst_7: is_scalar_tower ↝
 -/
#print subalgebra.of_under /- _inst_14: is_scalar_tower ↝
 -/
#print is_scalar_tower.range_under_adjoin /- _inst_7: is_scalar_tower ↝
 -/
#print algebra.fg_trans' /- _inst_7: is_scalar_tower ↝
 -/
#print submodule.smul_mem_span_smul_of_mem /- _inst_4: algebra ↝
_inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print submodule.smul_mem_span_smul /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print submodule.smul_mem_span_smul' /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print submodule.span_smul /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print linear_independent_smul /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_4: algebra ↝
_inst_7: is_scalar_tower ↝
 -/
#print is_basis.smul /- _inst_7: is_scalar_tower ↝
 -/
#print is_basis.smul_repr /- _inst_7: is_scalar_tower ↝
 -/
#print is_basis.smul_repr_mk /- _inst_7: is_scalar_tower ↝
 -/
#print exists_subalgebra_of_fg /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
_inst_3: comm_ring ↝ semiring
_inst_7: is_scalar_tower ↝
 -/
#print fg_of_fg_of_fg /- _inst_7: is_scalar_tower ↝
 -/

-- ring_theory\algebraic.lean
#print is_algebraic /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ semiring
 -/
#print algebra.is_algebraic_trans /- _inst_7: is_scalar_tower ↝
 -/
#print algebra.is_algebraic_of_finite /- _inst_2: field ↝ comm_ring
 -/
#print inv_eq_of_aeval_div_X_ne_zero /- _inst_3: field ↝ comm_semiring
_inst_4: field ↝ add_group comm_group_with_zero semiring
 -/

-- ring_theory\coprime.lean
#print is_coprime /- _inst_1: comm_semiring ↝ has_one has_add has_mul
 -/
#print is_coprime.add_mul_left_left /- _inst_1: comm_ring ↝ ring comm_semiring
 -/

-- ring_theory\derivation.lean
#print derivation.has_coe_to_fun /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.has_coe_to_linear_map /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.to_fun_eq_coe /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.coe_fn_coe /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.coe_injective /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.ext /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.map_add /- _inst_5: semimodule ↝
_inst_6: semimodule ↝ is_add_monoid_hom
_inst_7: is_scalar_tower ↝
 -/
#print derivation.map_zero /- _inst_5: semimodule ↝
_inst_6: semimodule ↝ is_add_monoid_hom
_inst_7: is_scalar_tower ↝
 -/
#print derivation.map_smul /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.leibniz /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.map_one_eq_zero /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.map_algebra_map /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.has_zero /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.inhabited /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.add_comm_monoid /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.add_apply /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.derivation.Rsemimodule /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.smul_to_linear_map_coe /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.Rsmul_apply /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.semimodule /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.smul_apply /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.is_scalar_tower /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_7: is_scalar_tower ↝
 -/
#print derivation.map_neg /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_2: comm_ring ↝ ring comm_semiring
_inst_7: is_scalar_tower ↝
 -/
#print derivation.map_sub /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_2: comm_ring ↝ ring comm_semiring
_inst_7: is_scalar_tower ↝
 -/
#print derivation.add_comm_group /- _inst_7: is_scalar_tower ↝
 -/
#print derivation.sub_apply /- _inst_7: is_scalar_tower ↝
 -/
#print linear_map.comp_der /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: is_scalar_tower ↝
_inst_11: is_scalar_tower ↝
 -/
#print linear_map.comp_der_apply /- _inst_5: semimodule ↝
_inst_6: semimodule ↝
_inst_8: semimodule ↝
_inst_9: semimodule ↝
_inst_10: is_scalar_tower ↝
_inst_11: is_scalar_tower ↝
 -/

-- ring_theory\discrete_valuation_ring.lean
#print discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization /- _inst_1: integral_domain ↝ monoid has_zero
 -/
#print discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.of_ufd_of_unique_irreducible /- _inst_2: unique_factorization_monoid ↝ wf_dvd_monoid
 -/
#print discrete_valuation_ring.unit_mul_pow_congr_pow /- _inst_2: discrete_valuation_ring ↝ unique_factorization_monoid
 -/

-- ring_theory\eisenstein_criterion.lean
#print polynomial.eisenstein_criterion_aux.map_eq_C_mul_X_pow_of_forall_coeff_mem /- _inst_1: integral_domain ↝ comm_ring
 -/
#print polynomial.eisenstein_criterion_aux.le_nat_degree_of_map_eq_mul_X_pow /- _inst_1: integral_domain ↝ comm_ring
 -/
#print polynomial.eisenstein_criterion_aux.eval_zero_mem_ideal_of_eq_mul_X_pow /- _inst_1: integral_domain ↝ comm_ring
 -/
#print polynomial.eisenstein_criterion_aux.is_unit_of_nat_degree_eq_zero_of_forall_dvd_is_unit /- _inst_1: integral_domain ↝ ring comm_semiring
 -/

-- ring_theory\finiteness.lean
#print module.finite /- _inst_1: comm_ring ↝ ring
 -/
#print algebra.finite_type /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ semiring
 -/
#print module.finite.trans /- _inst_4: comm_ring ↝ semiring add_comm_group
_inst_5: algebra ↝
_inst_10: algebra ↝
_inst_11: is_scalar_tower ↝
 -/
#print algebra.finite_type.trans /- _inst_11: is_scalar_tower ↝
 -/
#print ring_hom.finite /- _inst_2: comm_ring ↝ add_comm_group comm_semiring
 -/
#print alg_hom.finite /- _inst_1: comm_ring ↝ comm_semiring
 -/
#print alg_hom.finite_type /- _inst_1: comm_ring ↝ comm_semiring
 -/

-- ring_theory\fintype.lean
#print card_units_lt /- _inst_1: semiring ↝ monoid_with_zero
 -/

-- ring_theory\fractional_ideal.lean
#print ring.fractional_ideal.nontrivial /- _inst_3: integral_domain ↝ comm_ring
_inst_4: field ↝ nontrivial comm_ring
 -/
#print ring.fractional_ideal.fractional_div_of_nonzero /- _inst_4: field ↝ comm_ring no_zero_divisors
 -/
#print ring.fractional_ideal.mul_generator_self_inv /- _inst_3: integral_domain ↝ comm_ring
 -/
#print ring.fractional_ideal.is_principal /- _inst_6: is_principal_ideal_ring ↝ submodule.is_principal
 -/
#print ring.fractional_ideal.is_noetherian_zero /- _inst_3: integral_domain ↝ comm_ring
 -/
#print ring.fractional_ideal.is_noetherian_iff /- _inst_3: integral_domain ↝ comm_ring
 -/
#print ring.fractional_ideal.is_noetherian_coe_to_fractional_ideal /- _inst_5: is_noetherian_ring ↝ is_noetherian
 -/

-- ring_theory\ideal\basic.lean
#print ideal /- _inst_1: comm_ring ↝ semiring
 -/
#print ideal.span_singleton_eq_span_singleton /- _inst_2: integral_domain ↝ cancel_monoid_with_zero comm_ring
 -/
#print ideal.bot_prime /- _inst_2: integral_domain ↝ nontrivial comm_ring no_zero_divisors
 -/
#print ideal.span_singleton_lt_span_singleton /- _inst_2: integral_domain ↝ comm_cancel_monoid_with_zero comm_ring
 -/
#print ideal.factors_decreasing /- _inst_2: integral_domain ↝ cancel_monoid_with_zero comm_ring
 -/
#print ideal.eq_bot_or_top /- _inst_2: field ↝ group_with_zero comm_ring
 -/
#print ring.exists_not_is_unit_of_not_is_field /- _inst_1: comm_ring ↝ comm_monoid ring
 -/
#print mem_nonunits_iff /- _inst_1: comm_monoid ↝ monoid
 -/
#print zero_mem_nonunits /- _inst_1: semiring ↝ monoid_with_zero
 -/
#print field.local_ring /- _inst_1: field ↝ group_with_zero comm_ring
 -/

-- ring_theory\ideal\operations.lean
#print submodule.annihilator /- _inst_3: module ↝
 -/
#print submodule.colon /- _inst_3: module ↝
 -/
#print submodule.mem_annihilator /- _inst_3: module ↝
 -/
#print submodule.annihilator_eq_top_iff /- _inst_3: module ↝
 -/
#print submodule.mem_colon /- _inst_3: module ↝
 -/
#print submodule.mem_smul_span_singleton /- _inst_3: module ↝
 -/
#print submodule.smul_bot /- _inst_3: module ↝
 -/
#print submodule.top_smul /- _inst_3: module ↝
 -/
#print submodule.smul_sup /- _inst_3: module ↝
 -/
#print submodule.smul_assoc /- _inst_3: module ↝
 -/
#print submodule.span_smul_span /- _inst_3: module ↝
 -/
#print ideal.mul_eq_bot /- _inst_2: integral_domain ↝ comm_ring no_zero_divisors
 -/
#print ring_hom.ker_is_prime /- _inst_2: integral_domain ↝ nontrivial comm_ring no_zero_divisors
 -/

-- ring_theory\ideal\over.lean
#print ideal.exists_coeff_ne_zero_mem_comap_of_root_mem /- _inst_2: integral_domain ↝ comm_ring no_zero_divisors
 -/
#print ideal.exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff /- _inst_2: integral_domain ↝ comm_ring
 -/
#print ideal.mem_of_one_mem /- _inst_2: integral_domain ↝ comm_ring
 -/
#print ideal.is_maximal_comap_of_is_integral_of_is_maximal /- _inst_2: integral_domain ↝ comm_ring ideal.is_prime
 -/
#print ideal.exists_ideal_over_prime_of_is_integral /- _inst_2: integral_domain ↝ comm_ring
 -/

-- ring_theory\integral_closure.lean
#print ring_hom.is_integral_elem /- _inst_1: comm_ring ↝ semiring
_inst_2: ring ↝ semiring
 -/
#print is_integral_alg_hom /- _inst_2: comm_ring ↝ ring
_inst_3: comm_ring ↝ ring
 -/
#print is_integral_of_is_scalar_tower /- _inst_3: comm_ring ↝ ring
_inst_7: is_scalar_tower ↝
 -/
#print fg_adjoin_singleton_of_integral /- _inst_2: comm_ring ↝ is_subring ring comm_semiring
 -/
#print is_integral_zero /- _inst_2: comm_ring ↝ ring
 -/
#print is_integral_one /- _inst_2: comm_ring ↝ ring
 -/
#print is_integral_trans_aux /- _inst_2: comm_ring ↝ comm_semiring
 -/
#print is_integral_trans /- _inst_7: is_scalar_tower ↝
 -/
#print algebra.is_integral_trans /- _inst_7: is_scalar_tower ↝
 -/
#print is_integral_of_surjective /- _inst_2: comm_ring ↝ ring
 -/
#print is_integral_tower_bot_of_is_integral /- _inst_2: comm_ring ↝ ring comm_semiring
_inst_3: comm_ring ↝ ring comm_semiring
_inst_7: is_scalar_tower ↝
 -/
#print is_integral_tower_bot_of_is_integral_field /- _inst_9: field ↝ comm_ring division_ring
_inst_15: is_scalar_tower ↝
 -/
#print is_integral_tower_top_of_is_integral /- _inst_3: comm_ring ↝ ring
_inst_7: is_scalar_tower ↝
 -/
#print is_field_of_is_integral_of_is_field /- _inst_8: integral_domain ↝ nontrivial comm_ring
_inst_9: integral_domain ↝ nontrivial ring no_zero_divisors comm_semiring
 -/

-- ring_theory\integral_domain.lean
#print card_nth_roots_subgroup_units /- _inst_2: group ↝ monoid
 -/
#print field_of_integral_domain /- _inst_4: decidable_eq ↝
 -/
#print card_fiber_eq_of_mem_range /- _inst_5: decidable_eq ↝
 -/

-- ring_theory\localization.lean
#print localization_map.is_unit_comp /- _inst_3: comm_ring ↝ comm_monoid semiring
 -/
#print localization_map.eq_of_eq /- _inst_3: comm_ring ↝ comm_monoid semiring
 -/
#print localization_map.epic_of_localization_map /- _inst_3: comm_ring ↝ comm_monoid semiring
 -/
#print localization.has_zero /- _inst_1: comm_ring ↝ has_zero comm_monoid
 -/
#print localization_map.integer_normalization_eval₂_eq_zero /- _inst_4: comm_ring ↝ semiring
 -/
#print localization_map.integer_normalization_aeval_eq_zero /- _inst_7: is_scalar_tower ↝
 -/
#print fraction_map.mk'_eq_div /- _inst_4: integral_domain ↝ nontrivial comm_ring
_inst_6: field ↝ group_with_zero comm_ring
 -/
#print fraction_map.is_unit_map_of_injective /- _inst_4: integral_domain ↝ nontrivial comm_ring
_inst_7: field ↝ group_with_zero ring
 -/
#print fraction_map.lift /- _inst_6: field ↝ comm_ring
 -/
#print fraction_map.map /- _inst_6: field ↝ comm_ring
_inst_7: field ↝ comm_ring
 -/
#print fraction_map.field_equiv_of_ring_equiv /- _inst_6: field ↝ comm_ring
_inst_7: field ↝ comm_ring
 -/
#print fraction_map.comap_is_algebraic_iff /- _inst_7: field ↝ comm_ring
_inst_10: is_scalar_tower ↝
 -/
#print fraction_map.exists_reduced_fraction /- _inst_6: field ↝ cancel_monoid_with_zero comm_ring
 -/
#print integral_closure.fraction_map_of_finite_extension /- _inst_9: is_scalar_tower ↝
 -/
#print fraction_ring /- _inst_4: integral_domain ↝ monoid_with_zero comm_monoid
 -/
#print fraction_ring.of /- _inst_4: integral_domain ↝ comm_ring
 -/

-- ring_theory\matrix_algebra.lean
#print matrix.algebra /- _inst_5: decidable_eq ↝
 -/
#print algebra_map_matrix_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.to_fun_alg_hom /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.to_fun_alg_hom_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.inv_fun /- _inst_3: algebra ↝
_inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.inv_fun_zero /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.inv_fun_add /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.inv_fun_smul /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.inv_fun_algebra_map /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.right_inv /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.left_inv /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor.equiv /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor_apply /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor_apply_std_basis /- _inst_5: decidable_eq ↝
 -/
#print matrix_equiv_tensor_apply_symm /- _inst_5: decidable_eq ↝
 -/

-- ring_theory\multiplicity.lean
#print multiplicity /- _inst_1: comm_monoid ↝ has_dvd has_pow
_inst_2: decidable_rel ↝
 -/
#print multiplicity.finite /- _inst_1: comm_monoid ↝ has_dvd has_pow
 -/
#print multiplicity.finite_iff_dom /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.pow_dvd_of_le_multiplicity /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.pow_multiplicity_dvd /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.is_greatest /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.is_greatest' /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.unique /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.unique' /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.le_multiplicity_of_pow_dvd /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.pow_dvd_iff_le_multiplicity /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_lt_iff_neg_dvd /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.eq_some_iff /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.eq_top_iff /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.one_right /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.get_one_right /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_unit /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.one_left /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_eq_zero_of_not_dvd /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.eq_top_iff_not_finite /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_le_multiplicity_iff /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_le_multiplicity_of_dvd /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.dvd_of_multiplicity_pos /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.dvd_iff_multiplicity_pos /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.ne_zero_of_finite /- _inst_1: comm_monoid_with_zero ↝ monoid_with_zero comm_monoid
 -/
#print multiplicity.zero /- _inst_1: comm_monoid_with_zero ↝ monoid_with_zero comm_monoid
_inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_zero_eq_zero_of_ne_zero /- _inst_1: comm_monoid_with_zero ↝ monoid_with_zero comm_monoid
_inst_2: decidable_rel ↝
 -/
#print multiplicity.min_le_multiplicity_add /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.neg /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_add_of_gt /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_sub_of_gt /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_add_eq_min /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_self /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_monoid
_inst_2: decidable_rel ↝
 -/
#print multiplicity.get_multiplicity_self /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_monoid_with_zero
_inst_2: decidable_rel ↝
 -/
#print multiplicity.mul' /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.mul /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.finset.prod /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.pow' /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.pow /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_pow_self /- _inst_2: decidable_rel ↝
 -/
#print multiplicity.multiplicity_pow_self_of_prime /- _inst_2: decidable_rel ↝
 -/

-- ring_theory\noetherian.lean
#print submodule.fg /- _inst_3: semimodule ↝
 -/
#print submodule.fg_def /- _inst_3: semimodule ↝
 -/
#print submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul /- _inst_6: module ↝
 -/
#print submodule.fg_bot /- _inst_3: semimodule ↝
 -/
#print submodule.fg_sup /- _inst_3: semimodule ↝
 -/
#print submodule.fg_map /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print submodule.fg_top /- _inst_8: module ↝
 -/
#print submodule.fg_of_linear_equiv /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print submodule.fg_prod /- _inst_3: semimodule ↝
_inst_5: semimodule ↝
 -/
#print is_noetherian_submodule /- _inst_4: module ↝
 -/
#print is_noetherian_submodule_left /- _inst_4: module ↝
 -/
#print is_noetherian_submodule_right /- _inst_4: module ↝
 -/
#print is_noetherian_submodule' /- _inst_4: module ↝
 -/
#print is_noetherian_of_injective /- _inst_5: module ↝ is_noetherian
 -/
#print finite_of_linear_independent /- _inst_1: comm_ring ↝ ring
 -/
#print is_noetherian_ring /- _inst_1: ring ↝ semiring
 -/
#print is_noetherian_of_submodule_of_noetherian /- _inst_3: module ↝
 -/
#print is_noetherian_of_quotient_of_noetherian /- _inst_3: module ↝
 -/
#print is_noetherian_of_fg_of_noetherian /- _inst_3: module ↝
_inst_4: is_noetherian_ring ↝ is_noetherian
 -/
#print is_noetherian_of_fg_of_noetherian' /- _inst_3: module ↝
 -/
#print is_noetherian_span_of_finite /- _inst_3: module ↝
 -/
#print submodule.fg_mul /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: ring ↝ semiring
 -/
#print exists_prime_spectrum_prod_le /- _inst_2: is_noetherian_ring ↝ is_noetherian
 -/
#print exists_prime_spectrum_prod_le_and_ne_bot_of_domain /- _inst_4: is_noetherian_ring ↝ is_noetherian
 -/

-- ring_theory\non_zero_divisors.lean
#print mul_mem_non_zero_divisors /- _inst_1: comm_ring ↝ monoid_with_zero comm_semigroup
 -/
#print eq_zero_of_ne_zero_of_mul_right_eq_zero /- _inst_2: integral_domain ↝ has_zero no_zero_divisors has_mul
 -/
#print eq_zero_of_ne_zero_of_mul_left_eq_zero /- _inst_2: integral_domain ↝ has_zero no_zero_divisors has_mul
 -/
#print map_ne_zero_of_mem_non_zero_divisors /- _inst_1: comm_ring ↝ semiring
_inst_4: ring ↝ semiring
 -/
#print map_mem_non_zero_divisors /- _inst_2: integral_domain ↝ nontrivial comm_ring
 -/
#print le_non_zero_divisors_of_domain /- _inst_2: integral_domain ↝ monoid_with_zero has_add no_zero_divisors
 -/

-- ring_theory\polynomial\basic.lean
#print polynomial.degree_le /- _inst_1: comm_ring ↝ ring
 -/
#print polynomial.degree_lt /- _inst_1: comm_ring ↝ ring
 -/
#print polynomial.eval₂_restriction /- _inst_2: ring ↝ semiring
 -/
#print polynomial.linear_independent_powers_iff_eval₂ /- _inst_3: module ↝ algebra
 -/
#print polynomial.disjoint_ker_aeval_of_coprime /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_3: module ↝ algebra
 -/
#print polynomial.sup_aeval_range_eq_top_of_coprime /- _inst_3: module ↝ algebra
 -/
#print polynomial.sup_ker_aeval_le_ker_aeval_mul /- _inst_3: module ↝ algebra
 -/
#print polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime /- _inst_3: module ↝ algebra
 -/

-- ring_theory\polynomial\cyclotomic.lean
#print polynomial.prod_cyclotomic_eq_X_pow_sub_one /- _inst_1: comm_ring ↝ ring comm_semiring
 -/

-- ring_theory\polynomial\gauss_lemma.lean
#print polynomial.is_primitive.is_unit_iff_is_unit_map /- _inst_3: field ↝ integral_domain
 -/
#print polynomial.is_primitive.dvd_of_fraction_map_dvd_fraction_map /- _inst_3: field ↝ integral_domain
 -/

-- ring_theory\polynomial\rational_root.lean
#print scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero /- _inst_1: integral_domain ↝ comm_ring
 -/

-- ring_theory\polynomial\scale_roots.lean
#print scale_roots_eval₂_eq_zero /- _inst_3: comm_ring ↝ comm_monoid semiring
 -/
#print scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero /- _inst_1: integral_domain ↝ nontrivial comm_ring
_inst_2: field ↝ group_with_zero comm_ring
 -/

-- ring_theory\polynomial_algebra.lean
#print mat_poly_equiv /- _inst_4: decidable_eq ↝
 -/
#print mat_poly_equiv_coeff_apply_aux_1 /- _inst_4: decidable_eq ↝
 -/
#print mat_poly_equiv_coeff_apply_aux_2 /- _inst_4: decidable_eq ↝
 -/
#print mat_poly_equiv_coeff_apply /- _inst_4: decidable_eq ↝
 -/
#print mat_poly_equiv_symm_apply_coeff /- _inst_4: decidable_eq ↝
 -/
#print mat_poly_equiv_smul_one /- _inst_4: decidable_eq ↝
 -/

-- ring_theory\power_basis.lean
#print power_basis.finite_dimensional /- _inst_2: comm_ring ↝ ring
 -/
#print power_basis.findim /- _inst_2: comm_ring ↝ ring
 -/
#print power_basis.polynomial.mem_supported_range /- _inst_1: comm_ring ↝ semiring
 -/
#print power_basis.mem_span_pow' /- _inst_2: comm_ring ↝ semiring
 -/
#print power_basis.dim_ne_zero /- _inst_2: comm_ring ↝ ring
 -/
#print power_basis.dim_le_nat_degree_of_root /- _inst_8: integral_domain ↝ comm_ring
 -/
#print power_basis.nat_degree_lt_nat_degree /- _inst_1: comm_ring ↝ semiring
 -/
#print is_integral_algebra_map_iff /- _inst_2: comm_ring ↝ ring comm_semiring
_inst_3: comm_ring ↝ ring comm_semiring
_inst_7: is_scalar_tower ↝
 -/
#print minimal_polynomial.eq_of_algebra_map_eq /- _inst_2: comm_ring ↝ ring comm_semiring
_inst_3: comm_ring ↝ ring comm_semiring
_inst_16: is_scalar_tower ↝
 -/
#print algebra.linear_independent_power_basis /- _inst_2: comm_ring ↝ ring
 -/

-- ring_theory\power_series.lean
#print mv_power_series.has_one /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print mv_power_series.has_mul /- _inst_1: semiring ↝ add_comm_monoid has_mul
 -/
#print mv_power_series.X /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print mv_power_series.X_pow_dvd_iff /- _inst_1: comm_semiring ↝ semiring
 -/
#print mv_power_series.map.is_local_ring_hom /- _inst_1: comm_ring ↝ ring comm_semiring
_inst_2: comm_ring ↝ semiring
 -/
#print mv_power_series.inv /- _inst_1: field ↝ has_inv ring
 -/
#print power_series.eq_zero_or_eq_zero_of_mul_eq_zero /- _inst_1: integral_domain ↝ ring no_zero_divisors
 -/
#print polynomial.coe_to_power_series /- _inst_1: comm_semiring ↝ semiring
 -/

-- ring_theory\prime.lean
#print mul_eq_mul_prime_prod /- _inst_1: integral_domain ↝ cancel_monoid_with_zero comm_monoid_with_zero
_inst_2: decidable_eq ↝
 -/

-- ring_theory\principal_ideal_domain.lean
#print is_prime.to_maximal_ideal /- _inst_1: integral_domain ↝ cancel_monoid_with_zero comm_ring submodule.is_principal
_inst_2: is_principal_ideal_ring ↝ submodule.is_principal
 -/
#print principal_ideal_ring.is_noetherian_ring /- _inst_1: integral_domain ↝ comm_ring submodule.is_principal
_inst_2: is_principal_ideal_ring ↝ submodule.is_principal
 -/
#print principal_ideal_ring.is_maximal_of_irreducible /- _inst_1: integral_domain ↝ comm_ring submodule.is_principal
_inst_2: is_principal_ideal_ring ↝ submodule.is_principal
 -/

-- ring_theory\roots_of_unity.lean
#print is_primitive_root.gpow_eq_one /- _inst_3: comm_group ↝ comm_monoid
 -/
#print is_primitive_root.gpow_eq_one_iff_dvd /- _inst_3: comm_group ↝ group comm_monoid
 -/
#print is_primitive_root.inv /- _inst_3: comm_group ↝ group comm_monoid
 -/
#print is_primitive_root.fpow_eq_one /- _inst_4: comm_group_with_zero ↝ comm_monoid
 -/
#print is_primitive_root.fpow_eq_one_iff_dvd /- _inst_4: comm_group_with_zero ↝ group_with_zero comm_monoid
 -/
#print is_primitive_root.inv' /- _inst_4: comm_group_with_zero ↝ group_with_zero comm_monoid
 -/
#print is_primitive_root.mem_roots_of_unity /- _inst_5: integral_domain ↝ comm_monoid
 -/
#print is_primitive_root.pow /- _inst_5: integral_domain ↝ comm_monoid
 -/

-- ring_theory\subring.lean
#print subring.multiset_prod_mem /- _inst_4: comm_ring ↝ comm_monoid ring
 -/
#print subring.prod_mem /- _inst_4: comm_ring ↝ comm_monoid ring
 -/
#print ring_hom.restrict /- _inst_2: ring ↝ semiring
 -/
#print ring_hom.eq_of_eq_on_set_top /- _inst_2: ring ↝ semiring
 -/
#print subring.range_fst /- _inst_1: ring ↝ semiring
_inst_2: ring ↝ semiring
 -/
#print subring.range_snd /- _inst_1: ring ↝ semiring
_inst_2: ring ↝ semiring
 -/

-- ring_theory\subsemiring.lean
#print subsemiring.multiset_prod_mem /- _inst_4: comm_semiring ↝ comm_monoid semiring
 -/
#print subsemiring.prod_mem /- _inst_4: comm_semiring ↝ comm_monoid semiring
 -/

-- ring_theory\tensor_product.lean
#print algebra.tensor_product.mul_assoc' /- _inst_3: algebra ↝
_inst_5: algebra ↝
 -/

-- ring_theory\unique_factorization_domain.lean
#print is_noetherian_ring.wf_dvd_monoid /- _inst_2: is_noetherian_ring ↝ is_noetherian
 -/
#print prime_factors_irreducible /- _inst_1: comm_cancel_monoid_with_zero ↝ cancel_monoid_with_zero comm_monoid_with_zero
 -/
#print unique_factorization_monoid.factors /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.factors_prod /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.prime_of_factor /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.irreducible_of_factor /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.normalize_factor /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.factors_irreducible /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.exists_mem_factors_of_dvd /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.factors_zero /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.factors_one /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.factors_mul /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.factors_pow /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.dvd_iff_factors_le_factors /- _inst_2: decidable_eq ↝
 -/
#print unique_factorization_monoid.le_multiplicity_iff_repeat_le_factors /- _inst_5: decidable_eq ↝
_inst_6: decidable_rel ↝
 -/
#print unique_factorization_monoid.multiplicity_eq_count_factors /- _inst_5: decidable_eq ↝
_inst_6: decidable_rel ↝
 -/
#print associates.factor_set /- _inst_2: comm_cancel_monoid_with_zero ↝ comm_monoid_with_zero
 -/
#print associates.factor_set.sup_add_inf_eq_add /- _inst_2: decidable_eq ↝
 -/
#print associates.bcount /- _inst_2: decidable_eq ↝
 -/
#print associates.count /- _inst_2: decidable_eq ↝
 -/
#print associates.count_some /- _inst_2: decidable_eq ↝
 -/
#print associates.count_zero /- _inst_2: decidable_eq ↝
 -/
#print associates.count_reducible /- _inst_2: decidable_eq ↝
 -/
#print associates.factors' /- dec: decidable_eq ↝
 -/
#print associates.map_subtype_coe_factors' /- dec: decidable_eq ↝
 -/
#print associates.factors'_cong /- dec: decidable_eq ↝
 -/
#print associates.factors /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.factors_0 /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.factors_mk /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.prod_factors /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.factors_prod /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.eq_of_factors_eq_factors /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.factors_mul /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.factors_mono /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.factors_le /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.has_sup /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.has_inf /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.bounded_lattice /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.sup_mul_inf /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.dvd_of_mem_factors /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.dvd_of_mem_factors' /- dec: decidable_eq ↝
 -/
#print associates.mem_factors'_of_dvd /- dec: decidable_eq ↝
 -/
#print associates.mem_factors'_iff_dvd /- dec: decidable_eq ↝
 -/
#print associates.mem_factors_of_dvd /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.mem_factors_iff_dvd /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.exists_prime_dvd_of_not_inf_one /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.coprime_iff_inf_one /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.factors_prime_pow /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.prime_pow_dvd_iff_le /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.le_of_count_ne_zero /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.count_mul /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.count_of_coprime /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.count_mul_of_coprime /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.count_mul_of_coprime' /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.dvd_count_of_dvd_count_mul /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.factors_one /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.pow_factors /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.count_pow /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.dvd_count_pow /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print associates.is_pow_of_dvd_count /- dec: decidable_eq ↝
dec': decidable_eq ↝
 -/
#print unique_factorization_monoid.to_gcd_monoid /- _inst_5: decidable_eq ↝
_inst_6: decidable_eq ↝
 -/

-- ring_theory\valuation\basic.lean
#print valuation.zero_iff /- _inst_5: division_ring ↝ group_with_zero ring
 -/
#print valuation.ne_zero_iff /- _inst_5: division_ring ↝ group_with_zero ring
 -/
#print valuation.map_inv /- _inst_5: division_ring ↝ group_with_zero ring
 -/

-- ring_theory\valuation\integers.lean
#print valuation.integers.dvd_of_le /- _inst_1: field ↝ comm_ring division_ring
 -/

-- ring_theory\witt_vector\defs.lean
#print witt_vector.peval /- _inst_1: comm_ring ↝ ring comm_semiring
 -/

-- ring_theory\witt_vector\verschiebung.lean
#print witt_vector.verschiebung_fun /- _inst_1: comm_ring ↝ has_zero
 -/

-- ring_theory\witt_vector\witt_polynomial.lean
#print aeval_witt_polynomial /- _inst_3: comm_ring ↝ comm_semiring
 -/

-- set_theory\lists.lean
#print lists.decidable_eq /- _inst_1: decidable_eq ↝
 -/
#print lists.subset.decidable /- _inst_1: decidable_eq ↝
 -/
#print lists.mem.decidable /- _inst_1: decidable_eq ↝
 -/
#print finsets.decidable_eq /- _inst_1: decidable_eq ↝
 -/

-- set_theory\zfc.lean
#print Set.map_definable_aux /- H: pSet.definable ↝
 -/

-- tactic\abel.lean
#print tactic.abel.term /- _inst_1: add_comm_monoid ↝ has_zero has_add
 -/
#print tactic.abel.termg /- _inst_1: add_comm_group ↝ add_group
 -/
#print tactic.abel.smul /- _inst_1: add_comm_monoid ↝ has_zero has_add
 -/
#print tactic.abel.smulg /- _inst_1: add_comm_group ↝ add_group
 -/
#print tactic.abel.unfold_sub /- _inst_1: add_group ↝ has_sub has_neg has_add
 -/

-- tactic\cancel_denoms.lean
#print cancel_factors.mul_subst /- _inst_1: comm_ring ↝ comm_semigroup
 -/
#print cancel_factors.div_subst /- _inst_1: field ↝ comm_group_with_zero
 -/
#print cancel_factors.cancel_factors_eq_div /- _inst_1: field ↝ group_with_zero comm_semigroup
 -/
#print cancel_factors.add_subst /- _inst_1: ring ↝ distrib add_right_cancel_semigroup
 -/
#print cancel_factors.cancel_factors_eq /- _inst_1: linear_ordered_field ↝ group_with_zero comm_semigroup ordered_semiring
 -/

-- tactic\interval_cases.lean
#print tactic.interval_cases.set_elems /- _inst_1: decidable_eq ↝
 -/
#print tactic.interval_cases.mem_set_elems /- _inst_1: decidable_eq ↝
 -/

-- tactic\linarith\lemmas.lean
#print linarith.eq_of_eq_of_eq /- _inst_1: ordered_semiring ↝ add_monoid
 -/
#print linarith.le_of_eq_of_le /- _inst_1: ordered_semiring ↝ add_monoid has_le
 -/
#print linarith.lt_of_eq_of_lt /- _inst_1: ordered_semiring ↝ add_monoid has_lt
 -/
#print linarith.le_of_le_of_eq /- _inst_1: ordered_semiring ↝ add_monoid has_le
 -/
#print linarith.lt_of_lt_of_eq /- _inst_1: ordered_semiring ↝ add_monoid has_lt
 -/
#print linarith.mul_eq /- _inst_1: ordered_semiring ↝ has_lt mul_zero_class
 -/
#print linarith.mul_zero_eq /- _inst_1: semiring ↝ mul_zero_class
 -/
#print linarith.zero_mul_eq /- _inst_1: semiring ↝ mul_zero_class
 -/

-- tactic\monotonicity\lemmas.lean
#print lt_of_mul_lt_mul_neg_right /- _inst_1: linear_ordered_ring ↝ ring ordered_add_comm_group linear_ordered_semiring
 -/

-- tactic\norm_num.lean
#print norm_num.zero_succ /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print norm_num.one_succ /- _inst_1: semiring ↝ has_one has_add
 -/
#print norm_num.bit0_succ /- _inst_1: semiring ↝ has_one has_add
 -/
#print norm_num.bit1_succ /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.zero_adc /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print norm_num.adc_zero /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print norm_num.one_add /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.add_bit0_bit0 /- _inst_1: semiring ↝ add_comm_semigroup
 -/
#print norm_num.add_bit0_bit1 /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.add_bit1_bit0 /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.add_bit1_bit1 /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.adc_one_one /- _inst_1: semiring ↝ has_one has_add
 -/
#print norm_num.adc_bit0_one /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.adc_one_bit0 /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.adc_bit1_one /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.adc_one_bit1 /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.adc_bit0_bit0 /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.adc_bit1_bit0 /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.adc_bit0_bit1 /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.adc_bit1_bit1 /- _inst_1: semiring ↝ has_one add_comm_semigroup
 -/
#print norm_num.bit0_mul /- _inst_1: semiring ↝ distrib
 -/
#print norm_num.mul_bit0' /- _inst_1: semiring ↝ distrib
 -/
#print norm_num.mul_bit1_bit1 /- _inst_1: semiring ↝ monoid add_comm_semigroup distrib
 -/
#print norm_num.ne_zero_of_pos /- _inst_1: ordered_add_comm_group ↝ preorder has_zero
 -/
#print norm_num.clear_denom_div /- _inst_1: division_ring ↝ group_with_zero
 -/
#print norm_num.nonneg_pos /- _inst_1: ordered_cancel_add_comm_monoid ↝ preorder has_zero
 -/
#print norm_num.nat_cast_zero /- _inst_1: semiring ↝ has_one has_zero has_add
 -/
#print norm_num.nat_cast_one /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print norm_num.nat_cast_bit0 /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print norm_num.nat_cast_bit1 /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print norm_num.int_cast_zero /- _inst_1: ring ↝ has_one has_zero has_neg has_add
 -/
#print norm_num.int_cast_one /- _inst_1: ring ↝ add_monoid has_one has_neg
 -/
#print norm_num.int_cast_neg /- _inst_1: ring ↝ has_one add_group
 -/
#print norm_num.nat_cast_ne /- _inst_1: semiring ↝ add_monoid has_one
 -/
#print norm_num.int_cast_ne /- _inst_1: ring ↝ has_one add_group
 -/
#print norm_num.clear_denom_add /- _inst_1: division_ring ↝ cancel_monoid_with_zero distrib
 -/
#print norm_num.clear_denom_simple_nat /- _inst_1: division_ring ↝ monoid_with_zero nontrivial
 -/
#print norm_num.clear_denom_simple_div /- _inst_1: division_ring ↝ group_with_zero
 -/
#print norm_num.clear_denom_mul /- _inst_1: field ↝ cancel_monoid_with_zero comm_semigroup
 -/
#print norm_num.inv_one /- _inst_1: division_ring ↝ group_with_zero
 -/
#print norm_num.inv_one_div /- _inst_1: division_ring ↝ group_with_zero
 -/
#print norm_num.div_eq /- _inst_1: division_ring ↝ has_inv has_mul has_div
 -/
#print norm_num.sub_pos /- _inst_1: add_group ↝ has_sub has_neg has_add
 -/

-- tactic\ring.lean
#print tactic.ring.horner /- _inst_1: comm_semiring ↝ has_add has_mul has_pow
 -/
#print tactic.ring.horner_neg /- _inst_1: comm_ring ↝ ring comm_semiring
 -/
#print tactic.ring.pow_succ /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring.subst_into_pow /- _inst_1: monoid ↝ has_pow
 -/
#print tactic.ring.unfold_sub /- _inst_1: add_group ↝ has_sub has_neg has_add
 -/
#print tactic.ring.unfold_div /- _inst_1: division_ring ↝ has_inv has_mul has_div
 -/
#print tactic.ring.add_neg_eq_sub /- _inst_1: add_group ↝ has_sub has_neg has_add
 -/

-- tactic\ring_exp.lean
#print tactic.ring_exp.sum_congr /- _inst_1: comm_semiring ↝ is_commutative has_add
 -/
#print tactic.ring_exp.prod_congr /- _inst_1: comm_semiring ↝ is_commutative has_mul
 -/
#print tactic.ring_exp.exp_congr /- _inst_1: comm_semiring ↝ has_pow
 -/
#print tactic.ring_exp.base_to_exp_pf /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.exp_to_prod_pf /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.prod_to_sum_pf /- _inst_1: comm_semiring ↝ add_monoid
 -/
#print tactic.ring_exp.atom_to_sum_pf /- _inst_1: comm_semiring ↝ add_monoid monoid
 -/
#print tactic.ring_exp.mul_coeff_pf_one_mul /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.mul_coeff_pf_mul_one /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.add_overlap_pf /- _inst_1: comm_semiring ↝ distrib
 -/
#print tactic.ring_exp.add_overlap_pf_zero /- _inst_1: comm_semiring ↝ distrib mul_zero_class
 -/
#print tactic.ring_exp.add_pf_z_sum /- _inst_1: comm_semiring ↝ add_monoid
 -/
#print tactic.ring_exp.add_pf_sum_z /- _inst_1: comm_semiring ↝ add_monoid
 -/
#print tactic.ring_exp.add_pf_sum_overlap /- _inst_1: comm_semiring ↝ is_commutative has_add is_associative
 -/
#print tactic.ring_exp.add_pf_sum_overlap_zero /- _inst_1: comm_semiring ↝ add_monoid is_commutative
 -/
#print tactic.ring_exp.add_pf_sum_lt /- _inst_1: comm_semiring ↝ is_commutative has_add is_associative
 -/
#print tactic.ring_exp.add_pf_sum_gt /- _inst_1: comm_semiring ↝ is_commutative has_add is_associative
 -/
#print tactic.ring_exp.mul_pf_c_c /- _inst_1: comm_semiring ↝ is_commutative has_mul
 -/
#print tactic.ring_exp.mul_pf_c_prod /- _inst_1: comm_semiring ↝ is_commutative is_associative has_mul
 -/
#print tactic.ring_exp.mul_pf_prod_c /- _inst_1: comm_semiring ↝ is_commutative is_associative has_mul
 -/
#print tactic.ring_exp.mul_pp_pf_overlap /- _inst_1: comm_semiring ↝ monoid is_commutative
 -/
#print tactic.ring_exp.mul_pp_pf_prod_lt /- _inst_1: comm_semiring ↝ is_commutative is_associative has_mul
 -/
#print tactic.ring_exp.mul_pp_pf_prod_gt /- _inst_1: comm_semiring ↝ is_commutative is_associative has_mul
 -/
#print tactic.ring_exp.mul_p_pf_zero /- _inst_1: comm_semiring ↝ mul_zero_class
 -/
#print tactic.ring_exp.mul_p_pf_sum /- _inst_1: comm_semiring ↝ distrib
 -/
#print tactic.ring_exp.mul_pf_zero /- _inst_1: comm_semiring ↝ mul_zero_class
 -/
#print tactic.ring_exp.mul_pf_sum /- _inst_1: comm_semiring ↝ distrib
 -/
#print tactic.ring_exp.pow_e_pf_exp /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.pow_pp_pf_one /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.pow_pf_c_c /- _inst_1: comm_semiring ↝ has_pow
 -/
#print tactic.ring_exp.pow_pp_pf_c /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.pow_pp_pf_prod /- _inst_1: comm_semiring ↝ comm_monoid
 -/
#print tactic.ring_exp.pow_p_pf_one /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.pow_p_pf_zero /- _inst_1: comm_semiring ↝ monoid_with_zero
 -/
#print tactic.ring_exp.pow_p_pf_succ /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.pow_p_pf_singleton /- _inst_1: comm_semiring ↝ add_monoid has_pow
 -/
#print tactic.ring_exp.pow_p_pf_cons /- _inst_1: comm_semiring ↝ has_pow
 -/
#print tactic.ring_exp.pow_pf_zero /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.pow_pf_sum /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.simple_pf_sum_zero /- _inst_1: comm_semiring ↝ add_monoid
 -/
#print tactic.ring_exp.simple_pf_prod_one /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.simple_pf_var_one /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.simple_pf_exp_one /- _inst_1: comm_semiring ↝ monoid
 -/
#print tactic.ring_exp.inverse_pf /- _inst_2: division_ring ↝ has_inv
 -/
#print tactic.ring_exp.sub_pf /- _inst_2: ring ↝ has_sub has_neg has_add
 -/
#print tactic.ring_exp.div_pf /- _inst_2: division_ring ↝ has_inv has_mul has_div
 -/

-- tactic\where.lean
#print where.select_for_which /- _inst_1: decidable_eq ↝
 -/

-- testing\slim_check\functions.lean
#print slim_check.total_function.apply /- _inst_1: decidable_eq ↝
 -/
#print slim_check.total_function.shrink /- _inst_3: decidable_eq ↝
 -/
#print slim_check.total_function.pi.sampleable_ext /- _inst_3: decidable_eq ↝
 -/
#print slim_check.injective_function.apply /- _inst_1: decidable_eq ↝
 -/
#print slim_check.injective_function.list.apply_id /- _inst_1: decidable_eq ↝
 -/
#print slim_check.injective_function.list.apply_id_cons /- _inst_1: decidable_eq ↝
 -/
#print slim_check.injective_function.list.apply_id_zip_eq /- _inst_1: decidable_eq ↝
 -/
#print slim_check.injective_function.apply_id_mem_iff /- _inst_1: decidable_eq ↝
 -/
#print slim_check.injective_function.list.apply_id_eq_self /- _inst_1: decidable_eq ↝
 -/
#print slim_check.injective_function.apply_id_injective /- _inst_1: decidable_eq ↝
 -/
#print slim_check.injective_function.perm.slice /- _inst_1: decidable_eq ↝
 -/
#print slim_check.injective_function.shrink_perm /- _inst_1: decidable_eq ↝
 -/
#print slim_check.injective_function.shrink /- _inst_2: decidable_eq ↝
 -/
#print slim_check.injective_function.injective /- _inst_1: decidable_eq ↝
 -/

-- topology\algebra\affine.lean
#print affine_map.continuous_iff /- _inst_3: semimodule ↝
_inst_6: semimodule ↝
_inst_8: topological_add_group ↝ has_continuous_add has_continuous_sub
 -/
#print affine_map.line_map_continuous /- _inst_6: semimodule ↝
 -/

-- topology\algebra\continuous_functions.lean
#print continuous_subring /- _inst_4: topological_ring ↝ topological_add_group has_continuous_mul
 -/
#print continuous_has_scalar /- _inst_6: semimodule ↝
 -/
#print continuous_semimodule /- _inst_7: semimodule ↝
 -/
#print continuous_map_has_scalar /- _inst_6: semimodule ↝
 -/
#print continuous_map_semimodule /- _inst_7: semimodule ↝
 -/
#print continuous_has_scalar' /- _inst_6: semimodule ↝
 -/
#print continuous_map_has_scalar' /- _inst_6: semimodule ↝
 -/
#print continuous_map_module' /- _inst_8: semimodule ↝
 -/

-- topology\algebra\floor_ring.lean
#print continuous_on_fract /- _inst_4: topological_add_group ↝ has_continuous_sub
 -/
#print tendsto_fract_left' /- _inst_5: topological_add_group ↝ has_continuous_sub
 -/
#print tendsto_fract_right' /- _inst_5: topological_add_group ↝ has_continuous_sub
 -/

-- topology\algebra\group.lean
#print nhds_translation_mul_inv /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#print nhds_translation_add_neg /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#print quotient_add_group.is_open_map_coe /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#print quotient_group.is_open_map_coe /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#print is_open.add_left /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#print is_open.mul_left /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#print is_open.add_right /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#print is_open.mul_right /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#print topological_group.t1_space /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#print compact_open_separated_mul /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#print compact_open_separated_add /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#print compact_covered_by_mul_left_translates /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#print compact_covered_by_add_left_translates /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#print nhds_add /- _inst_2: add_comm_group ↝ has_continuous_add add_comm_semigroup add_group
 -/
#print nhds_mul /- _inst_2: comm_group ↝ comm_semigroup group has_continuous_mul
 -/

-- topology\algebra\group_with_zero.lean
#print filter.tendsto.div_const /- _inst_1: group_with_zero ↝ has_inv has_mul has_div
 -/
#print continuous_at.div_const /- _inst_1: group_with_zero ↝ has_inv has_mul has_div
 -/
#print continuous_on.div_const /- _inst_1: group_with_zero ↝ has_inv has_mul has_div
 -/
#print continuous.div_const /- _inst_1: group_with_zero ↝ has_inv has_mul has_div
 -/
#print filter.tendsto.div /- _inst_1: group_with_zero ↝ has_inv has_zero has_mul has_div
 -/
#print continuous.div /- _inst_1: group_with_zero ↝ has_inv has_zero has_mul has_div
 -/

-- topology\algebra\infinite_sum.lean
#print tsum_add_tsum_compl /- _inst_1: add_comm_group ↝ has_continuous_add add_comm_monoid add_group
_inst_3: topological_add_group ↝ has_continuous_add
 -/
#print has_sum.mul_left /- _inst_3: topological_semiring ↝ has_continuous_mul
 -/
#print has_sum.mul_right /- _inst_3: topological_semiring ↝ has_continuous_mul
 -/
#print has_sum_mul_left_iff /- _inst_1: division_ring ↝ group_with_zero semiring
 -/
#print has_sum_mul_right_iff /- _inst_1: division_ring ↝ group_with_zero semiring
 -/
#print summable_mul_left_iff /- _inst_1: division_ring ↝ group_with_zero semiring
 -/
#print summable_mul_right_iff /- _inst_1: division_ring ↝ group_with_zero semiring
 -/
#print summable_iff_cauchy_seq_finset /- _inst_1: add_comm_group ↝ add_comm_monoid
 -/

-- topology\algebra\module.lean
#print continuous_smul /- _inst_5: semimodule ↝
 -/
#print continuous.smul /- _inst_5: semimodule ↝
 -/
#print tendsto_smul /- _inst_5: semimodule ↝
 -/
#print filter.tendsto.smul /- _inst_5: semimodule ↝
 -/
#print topological_semiring.to_semimodule /- _inst_3: topological_semiring ↝ has_continuous_mul
 -/
#print topological_vector_space /- _inst_1: field ↝ ring
 -/
#print continuous_linear_map.linear_map.has_coe /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.to_fun /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_mk /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_mk' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.continuous /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_injective /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.injective_coe_fn /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.ext /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.ext_iff /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.map_zero /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.map_add /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.map_smul /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.map_sum /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_coe /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.eq_on_closure_span /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.ext_on /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.has_zero /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.inhabited /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.default_def /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.zero_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_zero /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_zero' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.unique_of_left /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.unique_of_right /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.id /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.has_one /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.one_def /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.id_apply /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.coe_id /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.coe_id' /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.one_apply /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.has_add /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.add_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_add /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_add' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.add_comm_monoid /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.sum_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.comp /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.coe_comp /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.coe_comp' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.comp_id /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.id_comp /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.comp_zero /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.zero_comp /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.comp_add /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.add_comp /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.comp_assoc /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_map.has_mul /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.mul_def /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.coe_mul /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.mul_apply /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.prod /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.coe_prod /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.prod_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.ker /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.ker_coe /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.mem_ker /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.is_closed_ker /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.apply_ker /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.is_complete_ker /- _inst_11: semimodule ↝
_inst_17: semimodule ↝
 -/
#print continuous_linear_map.complete_space_ker /- _inst_11: semimodule ↝
_inst_17: semimodule ↝
 -/
#print continuous_linear_map.ker_prod /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.range /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.range_coe /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.mem_range /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.range_prod_le /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.cod_restrict /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_cod_restrict /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_cod_restrict_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.ker_cod_restrict /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.subtype_val /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.coe_subtype_val /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.subtype_val_apply /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.fst /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.snd /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_fst /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_fst' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_snd /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_snd' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.fst_prod_snd /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.prod_map /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_map.coe_prod_map /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_map.coe_prod_map' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_map.coprod /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.coe_coprod /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.coprod_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.smul_right /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.smul_right_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.smul_right_one_one /- _inst_11: semimodule ↝
 -/
#print continuous_linear_map.smul_right_one_eq_iff /- _inst_11: semimodule ↝
 -/
#print continuous_linear_map.smul_right_comp /- _inst_11: semimodule ↝
 -/
#print continuous_linear_map.pi /- _inst_4: semimodule ↝
 -/
#print continuous_linear_map.pi_apply /- _inst_4: semimodule ↝
 -/
#print continuous_linear_map.pi_eq_zero /- _inst_4: semimodule ↝
 -/
#print continuous_linear_map.pi_zero /- _inst_4: semimodule ↝
 -/
#print continuous_linear_map.pi_comp /- _inst_4: semimodule ↝
_inst_7: semimodule ↝
 -/
#print continuous_linear_map.proj_pi /- _inst_7: semimodule ↝
 -/
#print continuous_linear_map.map_neg /- _inst_1: ring ↝ semiring
_inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.map_sub /- _inst_1: ring ↝ semiring
_inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.sub_apply' /- _inst_1: ring ↝ semiring
_inst_3: add_comm_group ↝ add_comm_monoid
_inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.range_prod_eq /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_map.has_neg /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.neg_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_neg /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_neg' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.add_comm_group /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.sub_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_sub /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_sub' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.ring /- _inst_10: semimodule ↝
 -/
#print continuous_linear_map.proj_ker_of_right_inverse /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.coe_proj_ker_of_right_inverse_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.proj_ker_of_right_inverse_apply_idem /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.proj_ker_of_right_inverse_comp_inv /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_map.smul_comp /- _inst_1: comm_ring ↝ ring
_inst_12: topological_module ↝ has_scalar
 -/
#print continuous_linear_map.smul_apply /- _inst_1: comm_ring ↝ ring
_inst_13: topological_module ↝ has_scalar
 -/
#print continuous_linear_map.coe_apply /- _inst_1: comm_ring ↝ ring
_inst_13: topological_module ↝ has_scalar
 -/
#print continuous_linear_map.coe_apply' /- _inst_1: comm_ring ↝ ring
_inst_13: topological_module ↝ has_scalar
 -/
#print continuous_linear_equiv.to_continuous_linear_map /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.continuous_linear_map.has_coe /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.has_coe_to_fun /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.coe_def_rev /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.coe_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.coe_to_linear_equiv /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.coe_coe /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.ext /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.to_homeomorph /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.map_zero /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.map_add /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.map_smul /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.map_eq_zero_iff /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.continuous /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.continuous_on /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.continuous_at /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.continuous_within_at /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.comp_continuous_on_iff /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.comp_continuous_iff /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.ext₁ /- _inst_10: semimodule ↝
 -/
#print continuous_linear_equiv.refl /- _inst_10: semimodule ↝
 -/
#print continuous_linear_equiv.coe_refl /- _inst_10: semimodule ↝
 -/
#print continuous_linear_equiv.coe_refl' /- _inst_10: semimodule ↝
 -/
#print continuous_linear_equiv.symm /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.symm_to_linear_equiv /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.trans /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_equiv.trans_to_linear_equiv /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_equiv.prod /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_equiv.prod_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_equiv.coe_prod /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_equiv.bijective /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.injective /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.surjective /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.trans_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_equiv.apply_symm_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.symm_apply_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.symm_trans_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_equiv.comp_coe /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
 -/
#print continuous_linear_equiv.coe_comp_coe_symm /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.coe_symm_comp_coe /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.symm_comp_self /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.self_comp_symm /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.symm_comp_self' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.self_comp_symm' /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.symm_symm /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.refl_symm /- _inst_10: semimodule ↝
 -/
#print continuous_linear_equiv.symm_symm_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.symm_apply_eq /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.eq_symm_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.equiv_of_inverse /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.equiv_of_inverse_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.symm_equiv_of_inverse /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
 -/
#print continuous_linear_equiv.automorphism_group /- _inst_10: semimodule ↝
 -/
#print continuous_linear_equiv.skew_prod /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_equiv.skew_prod_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_equiv.skew_prod_symm_apply /- _inst_10: semimodule ↝
_inst_11: semimodule ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_linear_equiv.map_sub /- _inst_4: semimodule ↝
_inst_7: semimodule ↝
 -/
#print continuous_linear_equiv.map_neg /- _inst_4: semimodule ↝
_inst_7: semimodule ↝
 -/
#print continuous_linear_equiv.of_unit /- _inst_4: semimodule ↝
 -/
#print continuous_linear_equiv.to_unit /- _inst_4: semimodule ↝
 -/
#print continuous_linear_equiv.units_equiv /- _inst_4: semimodule ↝
 -/
#print continuous_linear_equiv.units_equiv_apply /- _inst_4: semimodule ↝
 -/
#print continuous_linear_equiv.equiv_of_right_inverse /- _inst_4: semimodule ↝
_inst_7: semimodule ↝
 -/
#print continuous_linear_equiv.fst_equiv_of_right_inverse /- _inst_4: semimodule ↝
_inst_7: semimodule ↝
 -/
#print continuous_linear_equiv.snd_equiv_of_right_inverse /- _inst_4: semimodule ↝
_inst_7: semimodule ↝
 -/
#print continuous_linear_equiv.equiv_of_right_inverse_symm_apply /- _inst_4: semimodule ↝
_inst_7: semimodule ↝
 -/
#print continuous_linear_map.inverse /- _inst_5: semimodule ↝
_inst_7: semimodule ↝
 -/
#print continuous_linear_map.inverse_equiv /- _inst_5: semimodule ↝
_inst_7: semimodule ↝
 -/
#print continuous_linear_map.inverse_non_equiv /- _inst_5: semimodule ↝
_inst_7: semimodule ↝
 -/
#print submodule.closed_complemented /- _inst_4: module ↝
 -/
#print submodule.closed_complemented.has_closed_complement /- _inst_4: module ↝
 -/
#print submodule.closed_complemented.is_closed /- _inst_4: module ↝
 -/
#print submodule.closed_complemented_bot /- _inst_4: module ↝
 -/
#print submodule.closed_complemented_top /- _inst_4: module ↝
 -/
#print continuous_linear_map.closed_complemented_ker_of_right_inverse /- _inst_6: module ↝
 -/

-- topology\algebra\monoid.lean
#print submonoid.mem_nhds_one /- _inst_2: comm_monoid ↝ monoid
 -/
#print add_submonoid.mem_nhds_zero /- _inst_2: add_comm_monoid ↝ add_monoid
 -/

-- topology\algebra\multilinear.lean
#print continuous_multilinear_map.has_coe_to_fun /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.coe_continuous /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.coe_coe /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.to_multilinear_map_inj /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.ext /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.map_add /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.map_smul /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.map_coord_zero /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.map_zero /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.has_zero /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.inhabited /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.zero_apply /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.has_add /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.add_apply /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.add_comm_monoid /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.sum_apply /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.to_continuous_linear_map /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.prod /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_multilinear_map.prod_apply /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
_inst_13: semimodule ↝
 -/
#print continuous_multilinear_map.comp_continuous_linear_map /- _inst_1: decidable_eq ↝
_inst_14: semimodule ↝
 -/
#print continuous_multilinear_map.comp_continuous_linear_map_apply /- _inst_1: decidable_eq ↝
_inst_14: semimodule ↝
 -/
#print continuous_multilinear_map.cons_add /- _inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.cons_smul /- _inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.map_piecewise_add /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.map_add_univ /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.map_sum_finset /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.map_sum /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
 -/
#print continuous_multilinear_map.restrict_scalars /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
_inst_24: semimodule ↝
_inst_26: is_scalar_tower ↝
 -/
#print continuous_multilinear_map.coe_restrict_scalars /- _inst_1: decidable_eq ↝
_inst_12: semimodule ↝
_inst_24: semimodule ↝
_inst_26: is_scalar_tower ↝
 -/
#print continuous_multilinear_map.map_sub /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print continuous_multilinear_map.has_neg /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print continuous_multilinear_map.neg_apply /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print continuous_multilinear_map.add_comm_group /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print continuous_multilinear_map.sub_apply /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print continuous_multilinear_map.map_piecewise_smul /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print continuous_multilinear_map.map_smul_univ /- _inst_1: decidable_eq ↝
_inst_6: semimodule ↝
 -/
#print continuous_multilinear_map.has_scalar /- _inst_1: decidable_eq ↝
_inst_13: semimodule ↝
_inst_14: semimodule ↝
_inst_15: is_scalar_tower ↝
 -/
#print continuous_multilinear_map.smul_apply /- _inst_1: decidable_eq ↝
_inst_11: algebra ↝ has_scalar
_inst_13: semimodule ↝
_inst_14: semimodule ↝
_inst_15: is_scalar_tower ↝ has_scalar
_inst_17: topological_semimodule ↝ has_scalar
 -/
#print continuous_multilinear_map.is_scalar_tower /- _inst_1: decidable_eq ↝
_inst_11: algebra ↝ has_scalar
_inst_13: semimodule ↝
_inst_14: semimodule ↝
_inst_15: is_scalar_tower ↝ has_scalar
_inst_17: topological_semimodule ↝ has_scalar
_inst_20: algebra ↝ has_scalar
_inst_21: semimodule ↝
_inst_22: is_scalar_tower ↝ has_scalar
_inst_23: is_scalar_tower ↝
_inst_25: topological_semimodule ↝ has_scalar
 -/
#print continuous_multilinear_map.semimodule /- _inst_1: decidable_eq ↝
_inst_13: semimodule ↝
_inst_14: semimodule ↝
_inst_15: is_scalar_tower ↝
 -/
#print continuous_multilinear_map.to_multilinear_map_linear /- _inst_1: decidable_eq ↝
_inst_13: semimodule ↝
_inst_14: semimodule ↝
_inst_15: is_scalar_tower ↝
 -/
#print continuous_linear_map.comp_continuous_multilinear_map /- _inst_1: decidable_eq ↝
 -/
#print continuous_linear_map.comp_continuous_multilinear_map_coe /- _inst_1: decidable_eq ↝
 -/

-- topology\algebra\open_subgroup.lean
#print submodule.is_open_mono /- _inst_1: comm_ring ↝ ring
_inst_4: topological_add_group ↝ has_continuous_add
 -/
#print ideal.is_open_of_open_subideal /- _inst_3: topological_ring ↝ topological_add_group
 -/

-- topology\algebra\ordered.lean
#print preorder.topology /- _inst_1: preorder ↝ has_lt
 -/
#print order_dual.order_topology /- _inst_2: partial_order ↝ preorder
 -/
#print is_open_iff_generate_intervals /- _inst_2: partial_order ↝ preorder
 -/
#print nhds_eq_order /- _inst_2: partial_order ↝ preorder
 -/
#print tendsto_Ico_class_nhds /- _inst_2: partial_order ↝ preorder
t: order_topology ↝ filter.tendsto_Ixx_class
 -/
#print tendsto_Ioc_class_nhds /- _inst_2: partial_order ↝ preorder
t: order_topology ↝ filter.tendsto_Ixx_class
 -/
#print tendsto_Ioo_class_nhds /- _inst_2: partial_order ↝ preorder
t: order_topology ↝ filter.tendsto_Ixx_class
 -/
#print tendsto_Ixx_nhds_within /- _inst_2: partial_order ↝ preorder
 -/
#print induced_order_topology' /- _inst_1: partial_order ↝ preorder
 -/
#print order_topology.t2_space /- _inst_2: linear_order ↝ t2_space preorder
_inst_3: order_topology ↝ t2_space
 -/
#print Iio_mem_nhds /- _inst_3: order_topology ↝ order_closed_topology
 -/
#print Ioi_mem_nhds /- _inst_3: order_topology ↝ order_closed_topology
 -/
#print Ioo_mem_nhds /- _inst_3: order_topology ↝ order_closed_topology
 -/
#print continuous_right_of_strict_mono_surjective /- _inst_3: order_topology ↝ order_closed_topology
 -/
#print tendsto_at_top_add_tendsto_left /- _inst_2: linear_ordered_ring ↝ no_bot_order ordered_add_comm_group
 -/
#print tendsto_at_bot_add_tendsto_left /- _inst_2: linear_ordered_ring ↝ ordered_add_comm_group no_top_order
 -/
#print tendsto_at_top_mul_left /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print tendsto_at_top_mul_right /- _inst_1: linear_ordered_semiring ↝ linear_order ordered_semiring
 -/
#print neg_preimage_closure /- _inst_2: ordered_add_comm_group ↝ add_group
 -/
#print is_compact.bdd_above /- _inst_9: order_topology ↝ order_closed_topology
 -/
#print Sup_mem_closure /- _inst_9: complete_linear_order ↝ complete_lattice linear_order
 -/
#print Inf_mem_closure /- _inst_9: complete_linear_order ↝ complete_lattice linear_order
 -/
#print is_closed.Sup_mem /- _inst_9: complete_linear_order ↝ complete_lattice linear_order
 -/
#print is_closed.Inf_mem /- _inst_9: complete_linear_order ↝ complete_lattice linear_order
 -/
#print map_Sup_of_continuous_at_of_monotone' /- _inst_1: complete_linear_order ↝ complete_lattice linear_order
_inst_4: complete_linear_order ↝ complete_lattice linear_order
 -/
#print cSup_mem_closure /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order
 -/
#print cInf_mem_closure /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order
 -/
#print is_closed.cSup_mem /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order
 -/
#print is_closed.cInf_mem /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order
 -/
#print map_cSup_of_continuous_at_of_monotone /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order
_inst_4: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order
 -/
#print is_connected.Ioo_cInf_cSup_subset /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order order_closed_topology
_inst_3: order_topology ↝ order_closed_topology
 -/
#print is_preconnected.Ioi_cInf_subset /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order order_closed_topology
_inst_3: order_topology ↝ order_closed_topology
 -/
#print intermediate_value_Icc /- _inst_4: conditionally_complete_linear_order ↝ linear_order order_closed_topology
_inst_6: order_topology ↝ order_closed_topology
 -/
#print intermediate_value_Icc' /- _inst_4: conditionally_complete_linear_order ↝ linear_order order_closed_topology
_inst_6: order_topology ↝ order_closed_topology
 -/
#print is_compact.is_glb_Inf /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order order_closed_topology
_inst_3: order_topology ↝ order_closed_topology
 -/
#print Limsup_nhds /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice linear_order
 -/
#print tendsto_of_liminf_eq_limsup /- _inst_1: complete_linear_order ↝ order_top conditionally_complete_linear_order order_bot
 -/
#print tendsto_at_top_supr /- _inst_3: complete_linear_order ↝ order_top conditionally_complete_linear_order
 -/
#print tendsto_at_top_infi /- _inst_3: complete_linear_order ↝ conditionally_complete_linear_order order_bot
 -/
#print supr_eq_of_tendsto /- _inst_4: nonempty ↝ filter.ne_bot
_inst_5: semilattice_sup ↝ preorder filter.ne_bot
 -/
#print infi_eq_of_tendsto /- _inst_4: nonempty ↝ filter.ne_bot
_inst_5: semilattice_sup ↝ preorder filter.ne_bot
 -/
#print continuous_within_at_Iio_iff_Iic /- _inst_2: linear_order ↝ partial_order
 -/

-- topology\algebra\polynomial.lean
#print polynomial.tendsto_infinity /- _inst_1: comm_ring ↝ ring comm_semiring
 -/
#print polynomial.continuous_eval /- _inst_1: comm_semiring ↝ has_continuous_add semiring has_continuous_mul
_inst_3: topological_semiring ↝ has_continuous_add has_continuous_mul
 -/

-- topology\algebra\ring.lean
#print topological_ring.to_topological_semiring /- t: topological_ring ↝ has_continuous_add has_continuous_mul
 -/
#print mul_left_continuous /- _inst_3: topological_ring ↝ has_continuous_mul
 -/
#print mul_right_continuous /- _inst_3: topological_ring ↝ has_continuous_mul
 -/
#print quotient_ring.is_open_map_coe /- _inst_3: topological_ring ↝ has_continuous_add
 -/

-- topology\algebra\uniform_group.lean
#print add_comm_group.is_Z_bilin.comp_hom /- _inst_6: is_add_group_hom ↝ is_add_hom
 -/
#print is_Z_bilin.tendsto_zero_left /- _inst_5: uniform_space ↝ topological_space
 -/
#print is_Z_bilin.tendsto_zero_right /- _inst_5: uniform_space ↝ topological_space
 -/
#print tendsto_sub_comap_self /- _inst_2: add_comm_group ↝ add_group has_continuous_sub
_inst_3: topological_add_group ↝ has_continuous_sub
_inst_5: add_comm_group ↝ add_group
 -/

-- topology\algebra\uniform_ring.lean
#print uniform_space.completion.has_one /- _inst_1: ring ↝ has_one
 -/
#print uniform_space.completion.has_mul /- _inst_1: ring ↝ has_mul
 -/
#print uniform_space.completion.coe_mul /- _inst_3: topological_ring ↝ has_continuous_mul
 -/
#print uniform_space.completion.continuous_mul /- _inst_3: topological_ring ↝ topological_add_group has_continuous_mul
 -/

-- topology\bounded_continuous_function.lean
#print bounded_continuous_function /- _inst_2: metric_space ↝ topological_space has_dist
 -/
#print bounded_continuous_function.has_zero /- _inst_2: normed_group ↝ has_zero metric_space
 -/
#print bounded_continuous_function.has_scalar /- _inst_4: normed_space ↝
 -/
#print bounded_continuous_function.coe_smul /- _inst_4: normed_space ↝ has_scalar
 -/
#print bounded_continuous_function.smul_apply /- _inst_4: normed_space ↝ has_scalar
 -/
#print bounded_continuous_function.semimodule /- _inst_4: normed_space ↝
 -/
#print bounded_continuous_function.normed_space /- _inst_4: normed_space ↝
 -/
#print bounded_continuous_function.has_scalar' /- _inst_4: normed_space ↝
 -/
#print bounded_continuous_function.module' /- _inst_4: normed_space ↝
 -/
#print bounded_continuous_function.norm_smul_le /- _inst_4: normed_space ↝
 -/

-- topology\constructions.lean
#print continuous_update /- _inst_1: decidable_eq ↝
 -/

-- topology\metric_space\antilipschitz.lean
#print antilipschitz_with /- _inst_1: emetric_space ↝ has_edist
_inst_2: emetric_space ↝ has_edist
 -/

-- topology\metric_space\basic.lean
#print metric.ball /- _inst_1: metric_space ↝ has_dist
 -/
#print metric.closed_ball /- _inst_1: metric_space ↝ has_dist
 -/
#print metric.sphere /- _inst_1: metric_space ↝ has_dist
 -/
#print metric.complete_of_cauchy_seq_tendsto /- _inst_1: metric_space ↝ emetric_space
 -/
#print metric.bounded /- _inst_1: metric_space ↝ has_dist
 -/
#print metric.diam /- _inst_1: metric_space ↝ emetric_space
 -/

-- topology\metric_space\cau_seq_filter.lean
#print cau_seq.tendsto_limit /- _inst_1: normed_ring ↝ normed_group ring
 -/
#print cauchy_seq.is_cau_seq /- _inst_1: normed_field ↝ normed_group ring
 -/

-- topology\metric_space\closeds.lean
#print emetric.nonempty_compacts.second_countable_topology /- _inst_2: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/

-- topology\metric_space\completion.lean
#print metric.uniform_space.completion.has_dist /- _inst_1: metric_space ↝ uniform_space has_dist
 -/

-- topology\metric_space\contracting.lean
#print contracting_with.one_sub_K_pos /- _inst_1: metric_space ↝ emetric_space
 -/

-- topology\metric_space\emetric_space.lean
#print uniformity_dist_of_mem_uniformity /- _inst_1: linear_order ↝ has_lt
 -/
#print emetric.ball /- _inst_1: emetric_space ↝ has_edist
 -/
#print emetric.closed_ball /- _inst_1: emetric_space ↝ has_edist
 -/
#print emetric.diam /- _inst_1: emetric_space ↝ has_edist
 -/

-- topology\metric_space\hausdorff_distance.lean
#print emetric.inf_edist /- _inst_1: emetric_space ↝ has_edist
 -/
#print metric.inf_dist /- _inst_1: metric_space ↝ emetric_space
 -/
#print metric.inf_nndist /- _inst_1: metric_space ↝ emetric_space
 -/
#print metric.Hausdorff_dist /- _inst_1: metric_space ↝ emetric_space
 -/

-- topology\metric_space\isometry.lean
#print isometry /- _inst_1: emetric_space ↝ has_edist
_inst_2: emetric_space ↝ has_edist
 -/

-- topology\metric_space\lipschitz.lean
#print lipschitz_with /- _inst_1: emetric_space ↝ has_edist
_inst_2: emetric_space ↝ has_edist
 -/
#print lipschitz_on_with /- _inst_1: emetric_space ↝ has_edist
_inst_2: emetric_space ↝ has_edist
 -/

-- topology\sequences.lean
#print compact_space.tendsto_subseq /- _inst_2: topological_space.first_countable_topology ↝ seq_compact_space
_inst_3: compact_space ↝ seq_compact_space
 -/
#print metric.compact_iff_seq_compact /- _inst_1: metric_space ↝ emetric_space
 -/
#print metric.compact_space_iff_seq_compact_space /- _inst_1: metric_space ↝ emetric_space
 -/

-- topology\subset_properties.lean
#print is_connected_range /- _inst_3: connected_space ↝ preconnected_space nonempty
 -/
#print irreducible_space.connected_space /- _inst_3: irreducible_space ↝ preconnected_space nonempty
 -/

-- topology\uniform_space\abstract_completion.lean
#print abstract_completion.funext /- _inst_2: uniform_space ↝ topological_space
 -/
#print abstract_completion.extension₂_coe_coe /- _inst_4: separated_space ↝ t2_space
 -/

-- topology\uniform_space\basic.lean
#print uniform_space.is_open_ball /- _inst_1: uniform_space ↝ topological_space
 -/

-- topology\uniform_space\cauchy.lean
#print cauchy_seq /- _inst_2: semilattice_sup ↝ preorder
 -/
#print filter.tendsto.cauchy_seq /- _inst_3: nonempty ↝ filter.ne_bot
 -/
#print cauchy_seq_iff_tendsto /- _inst_2: nonempty ↝ filter.ne_bot
 -/

-- topology\uniform_space\complete_separated.lean
#print is_complete.is_closed /- _inst_2: separated_space ↝ t2_space
 -/
#print dense_inducing.continuous_extend_of_cauchy /- _inst_5: separated_space ↝ regular_space
 -/

-- topology\uniform_space\completion.lean
#print Cauchy.Cauchy_eq /- _inst_1: inhabited ↝ nonempty
 -/
#print uniform_space.completion.extension_coe /- _inst_4: separated_space ↝ t2_space
 -/

-- topology\uniform_space\uniform_embedding.lean
#print uniformly_extend_of_ind /- _inst_4: separated_space ↝ t2_space
 -/
#print uniformly_extend_unique /- _inst_4: separated_space ↝ t2_space
 -/
