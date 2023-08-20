/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.graph;

import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.BranchLocation;

import org.key_project.util.EqualsModProofIrrelevancy;

/**
 * A sequent formula tracked by the dependency graph.
 * The position in the sequent (antecedent / succedent)
 * and the position in the proof tree (branch location) are also stored.
 *
 * @author Arne Keller
 */
public class TrackedFormula extends GraphNode implements EqualsModProofIrrelevancy {
    /**
     * Symbol used to indicate the position of the formula in the sequent.
     *
     * @see #toString(boolean, boolean)
     */
    private static final String SEQ_ARROW = "⟹";

    /**
     * The formula.
     */
    public final SequentFormula formula;
    /**
     * Whether the formula is in the antecedent.
     */
    public final boolean inAntec;
    /**
     * Services object (required to print the formula).
     */
    public final Services services;

    /**
     * Construct a new tracked formula.
     *
     * @param formula sequent formula
     * @param branchLocation location where formula was derived
     * @param inAntec polarity of the sequent formula
     * @param services services
     */
    public TrackedFormula(
            SequentFormula formula,
            BranchLocation branchLocation,
            boolean inAntec,
            Services services) {
        super(branchLocation);
        this.formula = formula;
        this.inAntec = inAntec;
        this.services = services;
    }

    @Override
    public GraphNode popLastBranchID() {
        return new TrackedFormula(formula, branchLocation.removeLast(), inAntec, services);
    }

    @Override
    public String toString(boolean abbreviated, boolean omitBranch) {
        if (abbreviated) {
            return Integer.toHexString(hashCode());
        }
        String term = LogicPrinter.quickPrintTerm(
            formula.formula(),
            services,
            true, // pretty print
            true // using unicode symbols
        ).trim();
        if (!omitBranch) {
            term = term + branchLocation.toString();
        }
        return !inAntec ? (SEQ_ARROW + " " + term) : (term + " " + SEQ_ARROW);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        TrackedFormula that = (TrackedFormula) o;
        return inAntec == that.inAntec
                && formula == that.formula
                && Objects.equals(branchLocation, that.branchLocation);
    }

    @Override
    public int hashCode() {
        return Objects.hash(System.identityHashCode(formula), branchLocation, inAntec);
    }

    @Override
    public boolean equalsModProofIrrelevancy(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        TrackedFormula that = (TrackedFormula) o;
        return inAntec == that.inAntec
                && formula.equalsModProofIrrelevancy(that.formula)
                && Objects.equals(branchLocation, that.branchLocation);
    }

    @Override
    public int hashCodeModProofIrrelevancy() {
        return Objects.hash(inAntec, formula.hashCodeModProofIrrelevancy(), branchLocation);
    }
}
