/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;



/**
 * A sequent formula is a wrapper around a formula that occurs as top level formula in a sequent.
 * SequentFormula instances have to be unique in the sequent as they are used by PosInOccurrence to
 * determine the exact position. In earlier KeY versions this class was called ConstrainedFormula as
 * it was equipped with an additional constraints. It would be interesting to add more value to this
 * class by providing a way to add additional annotations or to cache local information about the
 * formula.
 */
public class SequentFormula extends org.key_project.prover.sequent.SequentFormula {

    /**
     * creates a new SequentFormula
     *
     * @param term a Term of sort {@link JavaDLTheory#FORMULA}
     */
    public SequentFormula(Term term) {
        super(term);
        if (term.sort() != JavaDLTheory.FORMULA
                && term.sort() != AbstractTermTransformer.METASORT) {
            throw new RuntimeException("A Term instead of a formula: " + term);
        }
    }

    public Term formula() {
        return (Term) super.formula();
    }
}
