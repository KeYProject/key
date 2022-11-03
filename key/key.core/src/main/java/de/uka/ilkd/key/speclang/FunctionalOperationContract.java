package de.uka.ilkd.key.speclang;


import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;


/**
 * A contract about an operation (i.e., a method or a constructor), consisting of a precondition, a
 * postcondition, a modifies clause, a measured-by clause, and a modality.
 */
public interface FunctionalOperationContract extends OperationContract {

    @Override
    public FunctionalOperationContract map(UnaryOperator<Term> op, Services services);

    /**
     * Returns the modality of the contract.
     */
    public Modality getModality();

    public boolean isReadOnlyContract(Services services);

    public Term getEnsures(LocationVariable heap);

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
    public Term getPost(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services);

    public Term getPost(List<LocationVariable> heapContext, ProgramVariable selfVar,
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
    public Term getPost(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services);

    public Term getPost(List<LocationVariable> heapContext, Map<LocationVariable, Term> heapTerms,
            Term selfTerm, ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services);

    public Term getFreePost(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services);

    public Term getFreePost(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services);

    public Term getFreePost(List<LocationVariable> heapContext,
            Map<LocationVariable, Term> heapTerms, Term selfTerm, ImmutableList<Term> paramTerms,
            Term resultTerm, Term excTerm, Map<LocationVariable, Term> atPres, Services services);

    Term getFreePost(List<LocationVariable> heapContext, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable excVar, Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services);

    /**
     * Returns the model method definition for model method contracts
     */
    public Term getRepresentsAxiom(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars, Services services);

    public Term getRepresentsAxiom(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Term resultTerm, Term excTerm,
            Map<LocationVariable, Term> atPres, Services services);

    public String getBaseName();

    public Term getPre();

    public Term getPost();

    public Term getMod();

    @Override
    public Term getMby();

    public Term getSelf();

    public ImmutableList<Term> getParams();

    public Term getResult();

    public Term getExc();

    public KeYJavaType getSpecifiedIn();

    public boolean hasResultVar();
}
