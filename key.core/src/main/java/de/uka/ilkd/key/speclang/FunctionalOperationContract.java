/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang;


import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A contract about an operation (i.e., a method or a constructor), consisting of a precondition, a
 * postcondition, a modifiable clause, a measured-by clause, and a modality.
 */
@NullMarked
public interface FunctionalOperationContract extends OperationContract {

    @Override
    FunctionalOperationContract map(UnaryOperator<JTerm> op, Services services);

    /**
     * Returns the modality of the contract.
     */
    JModality.JavaModalityKind getModalityKind();

    boolean isReadOnlyContract(Services services);

    @Nullable
    JTerm getEnsures(LocationVariable heap);

    /**
     * Returns the precondition of the contract.
     *
     * @param heap the heap variable.
     * @param selfVar the self variable.
     * @param paramVars the list of parameter variables.
     * @param atPreVars the map of old variables.
     * @param services the services object.
     * @return the precondition.
     */
    @Override
    @Nullable
    JTerm getPre(LocationVariable heap, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services);

    @Override
    @Nullable
    JTerm getPre(LocationVariable heap, JTerm heapTerm, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Map<LocationVariable, JTerm> atPres,
            Services services);

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
    @Nullable
    JTerm getPost(LocationVariable heap, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            @Nullable LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services);

    @Nullable
    JTerm getPost(List<LocationVariable> heapContext, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            @Nullable LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
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
    @Nullable
    JTerm getPost(LocationVariable heap, JTerm heapTerm, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm, @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    @Nullable
    JTerm getPost(List<LocationVariable> heapContext, Map<LocationVariable, JTerm> heapTerms,
            @Nullable JTerm selfTerm, ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm,
            @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    @Nullable
    JTerm getFreePost(LocationVariable heap, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            @Nullable LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services);

    @Nullable
    JTerm getFreePost(LocationVariable heap, JTerm heapTerm, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm, @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    @Nullable
    JTerm getFreePost(List<LocationVariable> heapContext,
            Map<LocationVariable, JTerm> heapTerms, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm, @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    @Nullable
    JTerm getFreePost(List<LocationVariable> heapContext,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            @Nullable LocationVariable excVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services);

    /**
     * Returns the modifiable clause of the contract.
     *
     * @param heapVar the heap variable.
     * @param selfVar the self variable.
     * @param paramVars the list of parameter variables.
     * @param services the services object.
     * @return the modifiable clause.
     */
    @Override
    @Nullable
    JTerm getModifiable(LocationVariable heapVar, @Nullable LocationVariable selfVar,
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
    @Override
    @Nullable
    JTerm getModifiable(LocationVariable heapVar, JTerm heapTerm, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, Services services);

    /**
     * Returns the free modifiable clause of the contract.
     *
     * @param heapVar the heap variable.
     * @param selfVar the self variable.
     * @param paramVars the list of parameter variables.
     * @param services the services object.
     * @return the free modifiable clause.
     */
    @Override
    @Nullable
    JTerm getFreeModifiable(LocationVariable heapVar, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, Services services);

    @Override
    @Nullable
    JTerm getFreeModifiable(LocationVariable heapVar, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms,
            Services services);

    /**
     * Returns the dependency set of the contract.
     *
     * @param heap the heap variable
     * @param atPre boolean whether old heap should be used
     * @param selfVar self variable
     * @param paramVars parameter variables
     * @param atPreVars variables at previous heap
     * @param services services object
     * @return the dependency set
     */
    @Override
    @Nullable
    JTerm getDep(LocationVariable heap, boolean atPre, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            @Nullable Map<LocationVariable, LocationVariable> atPreVars, Services services);

    @Override
    @Nullable
    JTerm getDep(LocationVariable heap, boolean atPre, JTerm heapTerm, @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, @Nullable Map<LocationVariable, JTerm> atPres,
            Services services);

    /**
     * Returns the model method definition for model method contracts
     */
    @Nullable
    JTerm getRepresentsAxiom(LocationVariable heap, @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars, @Nullable LocationVariable resultVar,
            Map<LocationVariable, LocationVariable> atPreVars, Services services);

    @Nullable
    JTerm getRepresentsAxiom(LocationVariable heap, JTerm heapTerm,
            @Nullable JTerm selfTerm,
            ImmutableList<JTerm> paramTerms, @Nullable JTerm resultTerm, @Nullable JTerm excTerm,
            Map<LocationVariable, JTerm> atPres, Services services);

    @Nullable
    String getBaseName();

    JTerm getPre();

    JTerm getPost();

    JTerm getModifiable();

    @Override
    @Nullable
    JTerm getMby();

    @Nullable
    JTerm getSelf();

    @Nullable
    ImmutableList<JTerm> getParams();

    @Nullable
    JTerm getResult();

    @Nullable
    JTerm getExc();

    KeYJavaType getSpecifiedIn();

    boolean hasResultVar();

    IProgramMethod getProgramMethod();
}
