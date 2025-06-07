/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;


import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.util.collection.ImmutableList;


/**
 * A contract about an operation (i.e., a method or a constructor), consisting of a precondition, a
 * postcondition, a modifiable clause, a measured-by clause, and a modality.
 */
public interface FunctionalOperationContract extends OperationContract {

    @Override
    FunctionalOperationContract map(UnaryOperator<JTerm> op, Services services);

    /**
     * Returns the modality of the contract.
     */
    JModality.JavaModalityKind getModalityKind();

    boolean isReadOnlyContract(Services services);

    JTerm getEnsures(LocationVariable heap);

    /**
     * Returns the postcondition of the contract.
     *
     * @param heap the heap variable.
     * @param selfVar the self variable.
     * @param paramVars the list of parameter variables.
     * @param resultVar the result variable.
     * @param excVar the exception variable.
     * @param atPreVars the map of old variables.
     * @param services the services object.
     * @return the post condition.
     */
    JTerm getPost(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services);

    JTerm getPost(List<LocationVariable> heapContext, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services);

    /**
     * Returns the postcondition of the contract.
     *
     * @param heap the heap variable.
     * @param heapTerm the heap variable term.
     * @param selfTerm the self variable term.
     * @param paramTerms the list of parameter variable terms.
     * @param resultTerm the result variable term.
     * @param excTerm the exception variable term.
     * @param atPres the map of old variable terms.
     * @param services the services object.
     * @return the postcondition.
     */
    JTerm getPost(LocationVariable heap, JTerm heapTerm, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, JTerm resultTerm, JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    JTerm getPost(List<LocationVariable> heapContext, Map<LocationVariable, JTerm> heapTerms,
            JTerm selfTerm, ImmutableList<JTerm> paramTerms, JTerm resultTerm, JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    JTerm getFreePost(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services);

    JTerm getFreePost(LocationVariable heap, JTerm heapTerm, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, JTerm resultTerm, JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    JTerm getFreePost(List<LocationVariable> heapContext,
            Map<LocationVariable, JTerm> heapTerms, JTerm selfTerm, ImmutableList<JTerm> paramTerms,
            JTerm resultTerm, JTerm excTerm, Map<LocationVariable, JTerm> atPres,
            Services services);

    JTerm getFreePost(List<LocationVariable> heapContext, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services);

    /**
     * Returns the model method definition for model method contracts
     */
    JTerm getRepresentsAxiom(LocationVariable heap, LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, LocationVariable resultVar,
            Map<LocationVariable, LocationVariable> atPreVars, Services services);

    JTerm getRepresentsAxiom(LocationVariable heap, JTerm heapTerm, JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, JTerm resultTerm, JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    String getBaseName();

    JTerm getPre();

    JTerm getPost();

    JTerm getModifiable();

    @Override
    JTerm getMby();

    JTerm getSelf();

    ImmutableList<JTerm> getParams();

    JTerm getResult();

    JTerm getExc();

    KeYJavaType getSpecifiedIn();

    boolean hasResultVar();

    IProgramMethod getProgramMethod();
}
