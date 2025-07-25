/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Quantifier;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termfeature.BinaryTermFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;


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
    protected boolean filter(Term t, MutableState mState, LogicServices services) {
        return containsExec(t, mState, services);
    }

    private boolean containsExec(Term t, MutableState mState, LogicServices services) {
        if (t.isRigid()) {
            return false;
        }
        // if ( t.isContainsJavaBlockRecursive() ) return true;

        final var op = t.op();
        switch (op) {
            case Quantifier ignored -> {
                return false;
            }
            case Modality ignored -> {
                return true;
            }
            case IProgramMethod ignored when considerQueries -> {
                return true;
            }
            default -> {
            }
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
