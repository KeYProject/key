/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Term;

public class SequentFormula {
    private final Term term;

    /**
     * creates a new SequentFormula
     *
     * @param term a Term of sort {@link RustyDLTheory#FORMULA}
     */
    public SequentFormula(Term term) {
        if (term.sort() != RustyDLTheory.FORMULA) {
            throw new RuntimeException("A Term instead of a formula: " + term);
        }
        this.term = term;
    }

    /** @return the stored Term */
    public Term formula() {
        return term;
    }

    /** String representation */
    public String toString() {
        return term.toString();
    }
}
