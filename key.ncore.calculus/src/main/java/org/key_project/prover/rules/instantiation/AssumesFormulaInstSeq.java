/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.instantiation;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;

/**
 * Instantiation of an assumes-formula that is present as a formula of the proof goal's sequent.
 * <p>
 * This instantiation kind is used if the formula used as an instantiation for one of the sequent's
 * assumes formulas is syntactically present. In that case the instantiation has not to be proven
 * to be valid as part of a separate proof goal.
 * </p>
 *
 * @see AssumesFormulaInstantiation,AssumesFormulaInstDirect
 */
public class AssumesFormulaInstSeq
        implements AssumesFormulaInstantiation {
    /**
     * Sequent and formula
     */
    private final Sequent seq;
    private final boolean antec; // formula is in antecedent?
    private final SequentFormula instantiation;

    public AssumesFormulaInstSeq(Sequent seq, boolean antec, SequentFormula instantiation) {
        this.seq = seq;
        this.antec = antec;
        this.instantiation = instantiation;
    }

    public AssumesFormulaInstSeq(Sequent instantiation, int indexPositionInSequent) {
        this(instantiation, instantiation.numberInAntec(indexPositionInSequent),
            instantiation.getFormulabyNr(indexPositionInSequent));
    }

    /**
     * @return the cf this is pointing to
     */
    @Override
    public SequentFormula getSequentFormula() {
        return instantiation;
    }

    @Override
    public String toString(LogicServices services) {
        return instantiation.formula().toString();
    }

    /**
     * Create a list with all formulas of a given semisequent
     */
    private static ImmutableArray<AssumesFormulaInstantiation> createListHelp(
            Sequent p_s,
            boolean antec) {
        Semisequent semi;
        if (antec) {
            semi = p_s.antecedent();
        } else {
            semi = p_s.succedent();
        }

        final AssumesFormulaInstSeq[] assumesInstFromSeq =
            new AssumesFormulaInstSeq[semi.size()];
        int i = assumesInstFromSeq.length - 1;

        for (final var sf : semi) {
            assumesInstFromSeq[i] = new AssumesFormulaInstSeq(p_s, antec, sf);
            --i;
        }

        return new ImmutableArray<>(assumesInstFromSeq);
    }

    public static ImmutableArray<AssumesFormulaInstantiation> createList(
            Sequent p_s, boolean antec) {
        return createListHelp(p_s, antec);
    }

    @Override
    public String toString() {
        return toString(null);
    }

    @Override
    public boolean equals(Object p_obj) {
        if (!(p_obj instanceof AssumesFormulaInstSeq other)) {
            return false;
        }
        return seq == other.seq && instantiation == other.instantiation && antec == other.antec;
    }

    @Override
    public int hashCode() {
        int result = 17;
        result = 37 * result + seq.hashCode();
        result = 37 * result + instantiation.hashCode();
        result = 37 * result + (antec ? 0 : 1);
        return result;
    }

    public boolean inAntec() {
        return antec;
    }

    private volatile PosInOccurrence pioCache = null;

    public PosInOccurrence toPosInOccurrence() {
        if (pioCache == null) {
            PosInOccurrence localPioCache =
                new PosInOccurrence(instantiation, PosInTerm.getTopLevel(), antec);
            pioCache = localPioCache;
        }
        return pioCache;
    }
}
