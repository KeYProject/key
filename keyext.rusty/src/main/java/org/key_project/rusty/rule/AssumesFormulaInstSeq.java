/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.LogicServices;
import org.key_project.logic.PosInTerm;
import org.key_project.prover.rules.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.rusty.Services;
import org.key_project.util.collection.ImmutableArray;

/**
 * Instantiation of an if-formula that is a formula of an existing sequent.
 */
public class AssumesFormulaInstSeq implements AssumesFormulaInstantiation {
    /**
     * Sequent and formula
     */
    private final org.key_project.prover.sequent.Sequent seq;
    private final boolean antec; // formula is in antecedent?
    private final SequentFormula cf;

    public AssumesFormulaInstSeq(org.key_project.prover.sequent.Sequent p_seq, boolean antec,
            SequentFormula p_cf) {
        seq = p_seq;
        this.antec = antec;
        cf = p_cf;
    }


    public AssumesFormulaInstSeq(org.key_project.prover.sequent.Sequent seq, int formulaNr) {
        this(seq, seq.numberInAntec(formulaNr), seq.getFormulabyNr(formulaNr));
    }


    /**
     * @return the cf this is pointing to
     */
    @Override
    public SequentFormula getSequentFormula() {
        return cf;
    }

    @Override
    public String toString(LogicServices services) {
        return cf.formula().toString();
    }

    /**
     * Create a list with all formulas of a given semisequent
     */
    private static ImmutableArray<AssumesFormulaInstantiation> createListHelp(
            org.key_project.prover.sequent.Sequent p_s,
            boolean antec) {
        Semisequent semi;
        if (antec) {
            semi = p_s.antecedent();
        } else {
            semi = p_s.succedent();
        }

        final AssumesFormulaInstSeq[] assumesInstFromSeq = new AssumesFormulaInstSeq[semi.size()];
        int i = assumesInstFromSeq.length - 1;

        for (final var sf : semi) {
            assumesInstFromSeq[i] = new AssumesFormulaInstSeq(p_s, antec, sf);
            --i;
        }

        return new ImmutableArray<>(assumesInstFromSeq);
    }

    public static ImmutableArray<AssumesFormulaInstantiation> createList(Sequent p_s, boolean antec,
            Services services) {
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
        return seq == other.seq && cf == other.cf && antec == other.antec;
    }

    @Override
    public int hashCode() {
        int result = 17;
        result = 37 * result + seq.hashCode();
        result = 37 * result + cf.hashCode();
        result = 37 * result + (antec ? 0 : 1);
        return result;
    }

    public boolean inAntec() {
        return antec;
    }

    private volatile PosInOccurrence pioCache = null;

    public PosInOccurrence toPosInOccurrence() {
        if (pioCache == null) {
            pioCache = new PosInOccurrence(cf, PosInTerm.getTopLevel(), antec);
        }
        return pioCache;
    }
}
