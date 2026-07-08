/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

/**
 * Symbolic-execution-internal ordering costs, used by {@link SymExStrategy}. These are the fine,
 * within-SE ordering values that deserve a speaking name of their own; the coarse priorities that
 * place SE rules relative to the other theories are written as
 * {@code CostBand.<band>.cost()/at(delta)} at the call site instead (e.g. block/loop contracts
 * {@code BLOCK_CONTRACT}, {@code loopInvariant} {@code LOOP_INVARIANT}, {@code concrete_java}
 * {@code REWRITE}).
 *
 * <p>
 * Values are byte-identical to the literals they replace. Changing one reorders symbolic execution;
 * verify with a full runAllProofs (as for
 * {@link org.key_project.prover.strategy.costbased.CostBand}).
 * </p>
 */
final class SymExCost {
    private SymExCost() {}

    /**
     * A cheap concrete program step: {@code simplify_expression}, {@code execute*Assignment} and
     * the ordinary {@code simplify_prog} case — "advance the program by one small step".
     */
    static final long PROGRAM_STEP = -100;

    /**
     * {@code simplify_prog} step that would raise a tracked runtime exception
     * (NullPointer/ArrayIndexOutOfBounds/…): pushed back so the non-exceptional path is explored
     * first.
     */
    static final long THROWING_PROGRAM_STEP = 500;

    /** {@code simplify_prog} step underneath a quantifier / non-atom: mildly dispreferred. */
    static final long PROGRAM_STEP_UNDER_QUANTIFIER = 200;

    /** Method-body expansion in METHOD_EXPAND mode. */
    static final long METHOD_EXPAND = 100;

    /**
     * Method-body expansion in METHOD_CONTRACT mode: raised (from {@link #METHOD_EXPAND}) so that
     * contract application is preferred over expanding the body.
     */
    static final long METHOD_EXPAND_REPRESSED = 2000;

    /** Preference offset of the method-contract feature ({@code methodSpec}). */
    static final long METHOD_CONTRACT_PREFERENCE = -20;

    /** {@code loop_scope_expand} when that loop treatment is selected. */
    static final long LOOP_SCOPE_EXPAND = 1000;

    /**
     * Tie-break so that in BLOCK_CONTRACT_EXTERNAL mode the external loop contract is applied in
     * preference to the internal one when both match; any small positive value would do.
     * <p>
     * TODO: this delta should be anchored to the external loop contract cost rather than standing
     * alone (deferred to the step-3 band normalization); kept byte-identical for now.
     * </p>
     */
    static final long LOOP_CONTRACT_INTERNAL_TIEBREAK = 42;

    /**
     * The merge rule ({@code MergeRule}), applied eagerly. NOT the EXECUTE band: that is reserved
     * for genuine program-execution rules, and a branch merge is not one.
     */
    static final long MERGE_RULE = -4000;

    /**
     * Deleting a merge point in MPS_SKIP mode: a delta below {@link #MERGE_RULE} so the skip is
     * preferred over performing a merge.
     */
    static final long MERGE_POINT_SKIP = MERGE_RULE - 1000;

    /**
     * Closing a modal tautology ({@code modal_tautology}). A distinct concept from a substitution;
     * it merely shares the numeric level of {@code CostBand.SUBST} and so gets its own name.
     */
    static final long MODAL_TAUTOLOGY = -10000;

    /** Prefer converting a box/diamond modality towards the antecedent-polarity program. */
    static final long BOX_DIAMOND_CONV = -1000;

    /** Mildly defer {@code split_if} so straight-line simplification runs first. */
    static final long SPLIT_IF = 50;
}
