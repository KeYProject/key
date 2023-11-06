/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * return zero cost if given term does not contain any free variables.
 */
public class ClosedExpressionTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new ClosedExpressionTermFeature();

    private ClosedExpressionTermFeature() {}

    protected boolean filter(Term term, Services services) {
        return term.freeVars().size() == 0;
    }
}
