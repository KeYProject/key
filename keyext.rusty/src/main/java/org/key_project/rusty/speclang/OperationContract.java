/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.function.UnaryOperator;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.util.collection.ImmutableList;

public interface OperationContract extends Contract {
    @Override
    ProgramFunction getTarget();

    @Override
    OperationContract map(UnaryOperator<Term> op, Services services);

    /**
     * Returns <code>true</code> iff the method (according to the contract) does not modify the heap
     * at all, i.e., iff it is "strictly pure."
     *
     * @return whether this contract is strictly pure.
     */
    boolean isPure();

    /**
     * Returns the modifiable clause of the contract.
     *
     * @param selfVar the self variable.
     * @param paramVars the list of parameter variables.
     * @param services the services object.
     * @return the modifiable clause.
     */
    Term getModifiable(Term selfVar,
            ImmutableList<Term> paramVars, Services services);
}
