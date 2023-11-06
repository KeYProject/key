/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.Quantifier;

public class AtomTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new AtomTermFeature();

    private AtomTermFeature() {}

    protected boolean filter(Term term, Services services) {
        final Operator op = term.op();
        return !(op instanceof Junctor || op == Equality.EQV || op instanceof IfThenElse
                || op instanceof Quantifier);
    }

}
