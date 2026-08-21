/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

/**
 * Why an instance is offered for a quantified formula.
 *
 * Every candidate instance enters the instantiation through one of the ways listed here. The
 * origin decides two things: whether the current {@link TriggerTreatment} admits the instance at
 * all, and what it costs on top of its predicted cost, see {@code Instantiation#surcharge}. An
 * origin that reads the instance off a term the formula itself names ranks before one that does
 * not.
 */
enum Origin {

    /** A term of the formula matched a sequent term structurally. */
    OWN_PATTERN,

    /**
     * A term of the formula matched a sequent term except at one position, and a theory solved
     * that position for the variable. The instance is a term the sequent does not contain.
     */
    SOLVED_POSITION,

    /** A theory's generalized trigger unified with a sequent term. */
    THEORY_UNIFIED,

    /**
     * A theory's generalized trigger matched a sequent term structurally, binding a
     * metavariable to a term the formula never named.
     */
    THEORY_MATCHED,

    /** A theory read the instance off the formula directly, without a trigger. */
    THEORY_DIRECT
}
