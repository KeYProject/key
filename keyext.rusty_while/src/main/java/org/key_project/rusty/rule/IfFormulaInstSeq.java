package org.key_project.rusty.rule;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.*;
import org.key_project.util.collection.ImmutableArray;

/**
 * Instantiation of an if-formula that is a formula of an existing sequent.
 */
public class IfFormulaInstSeq implements IfFormulaInstantiation{
    /**
     * Sequent and formula
     */
    private final Sequent seq;
    private final boolean antec; // formula is in antecedent?
    private final SequentFormula cf;

    public IfFormulaInstSeq(Sequent p_seq, boolean antec, SequentFormula p_cf) {
        seq = p_seq;
        this.antec = antec;
        cf = p_cf;
    }


    public IfFormulaInstSeq(Sequent seq, int formulaNr) {
        this(seq, seq.numberInAntec(formulaNr), seq.getFormulabyNr(formulaNr));
    }


    /**
     * @return the cf this is pointing to
     */
    @Override
    public SequentFormula getConstrainedFormula() {
        return cf;
    }

    @Override
    public String toString(Services services) {
        return "TODO";
    }

    /**
     * Create a list with all formulas of a given semisequent
     */
    private static ImmutableArray<IfFormulaInstantiation> createListHelp(Sequent p_s,
                                                                         boolean antec) {
        Semisequent semi;
        if (antec) {
            semi = p_s.antecedent();
        } else {
            semi = p_s.succedent();
        }

        final IfFormulaInstSeq[] assumesInstFromSeq = new IfFormulaInstSeq[semi.size()];
        int i = assumesInstFromSeq.length - 1;

        for (final var sf : semi) {
            assumesInstFromSeq[i] = new IfFormulaInstSeq(p_s, antec, sf);
            --i;
        }

        return new ImmutableArray<>(assumesInstFromSeq);
    }

    public static ImmutableArray<IfFormulaInstantiation> createList(Sequent p_s, boolean antec,
                                                                    Services services) {
        return createListHelp(p_s, antec);
    }

    @Override
    public String toString() {
        return toString(null);
    }

    @Override
    public boolean equals(Object p_obj) {
        if (!(p_obj instanceof IfFormulaInstSeq other)) {
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
            PosInOccurrence localPioCache = new PosInOccurrence(cf, PosInTerm.getTopLevel(), antec);
            pioCache = localPioCache;
        }
        return pioCache;
    }
}
