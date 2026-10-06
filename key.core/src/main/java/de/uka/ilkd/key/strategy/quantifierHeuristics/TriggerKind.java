/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

/**
 * How a uni-trigger is matched against the sequent.
 *
 * A trigger taken from the formula itself is matched structurally: each quantified variable is
 * bound to the subterm at its position. This binds every variable the trigger carries, so it is
 * only allowed when every one of them may be instantiated. A trigger that carries an existential
 * variable is unified instead, which treats that variable as an unknown rather than binding it.
 * A theory-derived trigger carries metavariables in place of ground subterms; unification binds
 * them on any target, and structural matching is allowed in addition under the most informed
 * treatment, since it instantiates from a term that does not occur in the formula.
 *
 * The kind is decided once, when the trigger is registered, and the matching stage chooses the
 * matcher by the kind alone.
 */
enum TriggerKind {

    /**
     * A term of the formula whose free variables are all universal. Matched structurally
     * against ground targets, unified against quantified ones.
     */
    PATTERN,

    /**
     * A theory's generalization, carrying metavariables. Unified against any target, and
     * additionally matched structurally against ground targets when the treatment allows it.
     */
    GENERALIZED,

    /**
     * A term of the formula carrying an existential variable. Unified against quantified
     * targets only; ground targets yield nothing.
     */
    NEEDS_UNIFY,

    /**
     * A theory's generalization that also carries an existential variable. Unified against any
     * target; never matched structurally.
     */
    GENERALIZED_UNIFY;

    /** Whether a theory derived this trigger rather than the formula containing it. */
    boolean isTheoryProvided() {
        return this == GENERALIZED || this == GENERALIZED_UNIFY;
    }
}
