/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.util.collection.ImmutableList;

public interface OperationContract extends Contract {

    @Override
    IProgramMethod getTarget();

    @Override
    OperationContract map(UnaryOperator<Term> op, Services services);

    /**
     * Returns <code>true</code> iff the method (according to the contract) does not modify the heap
     * at all, i.e., iff it is "strictly pure."
     *
     * @return whether this contract is strictly pure.
     */
    boolean hasModifiable(LocationVariable heap);

    /**
     * Returns <code>true</code> iff the method (according to a free clause of the contract) does
     * not modify the heap at all, i.e., iff it is freely "strictly pure."
     *
     * @return whether this contract is freely strictly pure.
     */
    boolean hasFreeModifiable(LocationVariable heap);

    /**
     * Returns the modifiable clause of the contract.
     *
     * @param heapVar the heap variable.
     * @param selfVar the self variable.
     * @param paramVars the list of parameter variables.
     * @param services the services object.
     * @return the modifiable clause.
     */
    Term getModifiable(LocationVariable heapVar, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services);

    /**
     * Returns the modifiable clause of the contract.
     *
     * @param heapVar the heap variable
     * @param heapTerm the heap variable term.
     * @param selfTerm the self variable term.
     * @param paramTerms the list of parameter variable terms.
     * @param services the services object.
     * @return the modifiable clause.
     */
    Term getModifiable(LocationVariable heapVar, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Services services);

    /**
     * Returns the free modifiable clause of the contract.
     *
     * @param heapVar the heap variable.
     * @param selfVar the self variable.
     * @param paramVars the list of parameter variables.
     * @param services the services object.
     * @return the free modifiable clause.
     */
    Term getFreeModifiable(LocationVariable heapVar, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Services services);

    /**
     * Returns the free modifiable clause of the contract.
     *
     * @param heapVar the heap variable
     * @param heapTerm the heap variable term.
     * @param selfTerm the self variable term.
     * @param paramTerms the list of parameter variable terms.
     * @param services the services object.
     * @return the free modifiable clause.
     */
    Term getFreeModifiable(LocationVariable heapVar, Term heapTerm,
            Term selfTerm,
            ImmutableList<Term> paramTerms,
            Services services);

    Term getFreePre(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services);

    Term getFreePre(List<LocationVariable> heapContext, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services);

    Term getFreePre(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres, Services services);
}
