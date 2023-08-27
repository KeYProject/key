/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;

/**
 * Term feature for testing equality of two terms. The feature returns zero iff it is invoked on a
 * term that is equal to the current value of <code>pattern</code>.
 *
 * NB: it is not possible to use general <code>ProjectionToTerm</code> here, because the information
 * necessary to evaluate a <code>ProjectionToTerm</code> is not available in a term feature
 */
public class EqTermFeature extends BinaryTermFeature {

    private final TermBuffer pattern;

    public static TermFeature create(TermBuffer pattern) {
        return new EqTermFeature(pattern);
    }

    private EqTermFeature(TermBuffer pattern) {
        this.pattern = pattern;
    }

    protected boolean filter(Term term, Services services) {
        return term.equalsModRenaming(pattern.getContent());
    }
}
