package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * A sequent formula is a wrapper around a formula that occurs as top level formula in a sequent.
 * SequentFormula instances have to be unique in the sequent as they are used by PosInOccurrence to
 * determine the exact position. In earlier KeY versions this class was called ConstrainedFormula as
 * it was equipped with an additional constraints. It would be interesting to add more value to this
 * class by providing a way to add additional annotations or to cache local information about the
 * formula.
 */
public class SequentFormula {

    private final Term term;

    private final int hashCode;

    /**
     * creates a new SequentFormula
     *
     * @param term a Term of sort {@link Sort#FORMULA}
     */
    public SequentFormula(Term term) {
        if (term.sort() != Sort.FORMULA && term.sort() != AbstractTermTransformer.METASORT) {
            throw new RuntimeException("A Term instead of a formula: " + term);
        }
        this.term = term;
        this.hashCode = term.hashCode() * 13;
    }

    /** @return the stored Term */
    public Term formula() {
        return term;
    }

    /** equal if terms and constraints are equal */
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj instanceof SequentFormula) {
            SequentFormula cmp = (SequentFormula) obj;
            return term.equals(cmp.formula());
        }
        return false;
    }

    /** String representation */
    public String toString() {
        return term.toString();
    }

    public int hashCode() {
        return hashCode;
    }
}
