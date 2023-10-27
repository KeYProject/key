/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;


import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.collection.ImmutableList;


/**
 * A contract about an operation (i.e., a method or a constructor), consisting of a precondition, a
 * postcondition, a modifies clause, a measured-by clause, and a modality.
 */
public interface FunctionalOperationContract extends OperationContract {

    @Override
    FunctionalOperationContract map(UnaryOperator<Term> op, Services services);

    /**
     * Returns the modality of the contract.
     */
    Modality getModality();

    boolean isReadOnlyContract(Services services);

    Term getEnsures(LocationVariable heap);

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
    Term getPost(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services);

    Term getPost(List<LocationVariable> heapContext, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, ? extends ProgramVariable> atPreVars,
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
    Term getPost(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services);

    Term getPost(List<LocationVariable> heapContext, Map<LocationVariable, Term> heapTerms,
            Term selfTerm, ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services);

    Term getFreePost(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services);

    Term getFreePost(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services);

    Term getFreePost(List<LocationVariable> heapContext,
            Map<LocationVariable, Term> heapTerms, Term selfTerm, ImmutableList<Term> paramTerms,
            Term resultTerm, Term excTerm, Map<LocationVariable, Term> atPres, Services services);

    Term getFreePost(List<LocationVariable> heapContext, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services);

    /**
     * Returns the model method definition for model method contracts
     */
    Term getRepresentsAxiom(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars, Services services);

    Term getRepresentsAxiom(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services);

    String getBaseName();

    Term getPre();

    Term getPost();

    Term getMod();

    @Override
    Term getMby();

    Term getSelf();

    ImmutableList<Term> getParams();

    Term getResult();

    Term getExc();

    KeYJavaType getSpecifiedIn();

    boolean hasResultVar();
}
