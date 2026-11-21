From BCE Require Import Graph Persistence Loops Canonical Induction Alias Representatives Fallback.

Print Assumptions Persistence.soundness.
Print Assumptions Persistence.known_at_arrival.
Print Assumptions Loops.loop_justified.
Print Assumptions Loops.invariant_back_ok.
Print Assumptions Canonical.canon_sound.
Print Assumptions Canonical.same_canonical_value.
Print Assumptions Canonical.guard_value_persists.
Print Assumptions Canonical.known_fact_on_ssa_values.
Print Assumptions Induction.phi_fact_justified.
Print Assumptions Induction.phi_fact_justified_with.
Print Assumptions Alias.alias_leaves_ok.
Print Assumptions Alias.alias_justified.
Print Assumptions Alias.phi_fact_justified_using_alias.
Print Assumptions Alias.alias_sound.
Print Assumptions Representatives.representatives_sound.
Print Assumptions Representatives.same_representative.
Print Assumptions Representatives.existing_truncation.
Print Assumptions Representatives.table_run_wf.
Print Assumptions Representatives.table_run_vbs_ok.
Print Assumptions Representatives.table_run_vbs_inj.
Print Assumptions Representatives.table_run_same_representative.
Print Assumptions Representatives.table_run_existing_truncation.
Print Assumptions Fallback.guard_complete_from_failing_check.
Print Assumptions Fallback.fallback_emission_sound.
Print Assumptions Fallback.fallback_never_unreachable.
Print Assumptions Fallback.fallback_verifier_sound.
