/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.strategy.feature.MutableState;
import org.jspecify.annotations.NonNull;


/**
 * Returns zero iff a term contains a program or (optionally) a query expression
 */
public class ContainsExecutableCodeTermFeature extends BinaryTermFeature {

    private final boolean considerQueries;

    private ContainsExecutableCodeTermFeature(boolean considerQueries) {
        this.considerQueries = considerQueries;
    }

    public final static TermFeature PROGRAMS = new ContainsExecutableCodeTermFeature(false);
    public final static TermFeature PROGRAMS_OR_QUERIES =
        new ContainsExecutableCodeTermFeature(true);

    @Override
    protected boolean filter(@NonNull Term t, MutableState mState, Services services) {
        return containsExec(t, mState, services);
    }

    private boolean containsExec(@NonNull Term t, MutableState mState, Services services) {
        if (t.isRigid()) {
            return false;
        }
        // if ( t.isContainsJavaBlockRecursive() ) return true;

        final Operator op = t.op();
        if (op instanceof Quantifier) {
            return false;
        }

        if (op instanceof Modality) {
            return true;
        }
        if (considerQueries && op instanceof IProgramMethod) {
            return true;
        }

        for (int i = 0; i != op.arity(); ++i) {
            final boolean res = filter(t.sub(i), mState, services);
            if (res) {
                return true;
            }
        }

        return false;
    }

}
