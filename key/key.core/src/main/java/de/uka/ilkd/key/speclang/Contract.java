// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * A contractual agreement about an ObserverFunction.
 */
public interface Contract extends SpecificationElement {

    public static final int INVALID_ID = Integer.MIN_VALUE;

    /**
     *
     * @return {@code true} if any only if this contract does not necessarily need to be proven in
     *         its own proof obligation. E.g., this is true for {@link FunctionalBlockContract}s and
     *         {@link FunctionalLoopContract}s.
     */
    default boolean isAuxiliary() {
        return false;
    }

    /**
     * Returns the id number of the contract. If a contract has instances for several methods
     * (inheritance!), all instances have the same id. The id is either non-negative or equal to
     * INVALID_ID.
     */
    public int id();

    /**
     * Returns the contracted function symbol.
     */
    public IObserverFunction getTarget();

    /**
     * Tells whether the contract contains a measured_by clause.
     */
    public boolean hasMby();

    /**
     * Returns the original ProgramVariables to replace them easier. The second list consists of the
     * parameters.
     */
    public OriginalVariables getOrigVars();

    /**
     * Returns the precondition of the contract.
     * @param heap heap variable
     * @param selfVar self variable
     * @param paramVars parameter variables
     * @param atPreVars variables at previous heap
     * @param services services object
     * @return precondition
     */
    public Term getPre(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars, Services services);

    /**
     * Returns the precondition of the contract.
     * @param heapContext heap context
     * @param selfVar self variable
     * @param paramVars parameter variables
     * @param atPreVars variables at previous heap
     * @param services services object
     * @return precondition
     */
    public Term getPre(List<LocationVariable> heapContext, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars, Services services);

    /**
     * Returns the precondition of the contract.
     * @param heap heap variable
     * @param heapTerm heap term
     * @param selfTerm self term
     * @param paramTerms parameter terms
     * @param atPres terms of variables at previous heap
     * @param services services object
     * @return the precondition
     */
    public Term getPre(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres, Services services);

    /**
     * Returns the precondition of the contract.
     * @param heapContext heap context
     * @param heapTerms heap terms
     * @param selfTerm term of self variable
     * @param paramTerms terms of parameter variables
     * @param atPres terms of variables at previous heap
     * @param services services object
     * @return the precondition
     */
    public Term getPre(List<LocationVariable> heapContext, Map<LocationVariable, Term> heapTerms,
            Term selfTerm, ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services);

    /**
     * Returns the dependency set of the contract.
     * @param heap the heap variable
     * @param atPre boolean whether old heap should be used
     * @param selfVar self variable
     * @param paramVars parameter variables
     * @param atPreVars variables at previous heap
     * @param services services object
     * @return the dependency set
     */
    public Term getDep(LocationVariable heap, boolean atPre, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars, Services services);

    /**
     * Returns the dependency set of the contract.
     * @param heap the heap variable
     * @param atPre boolean whether old heap should be used
     * @param heapTerm the heap variable term
     * @param selfTerm term of self variable
     * @param paramTerms terms of parameter variables
     * @param atPres terms of variables at previous heap
     * @param services services object
     * @return the dependency set
     */
    public Term getDep(LocationVariable heap, boolean atPre, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres, Services services);

    public Term getRequires(LocationVariable heap);

    public Term getAssignable(LocationVariable heap);

    public Term getAccessible(ProgramVariable heap);

    public Term getGlobalDefs();

    public Term getGlobalDefs(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Services services);

    public Term getMby();

    /**
     * Returns the measured_by clause of the contract.
     * @param selfVar the self variable
     * @param paramVars the parameter variables
     * @param services services object
     * @return the measured-by term
     */
    public Term getMby(ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Services services);

    /**
     * Returns the measured_by clause of the contract.
     * @param heapTerms terms for the heap context
     * @param selfTerm term of self variable
     * @param paramTerms terms of parameter variables
     * @param atPres terms of variables at previous heap
     * @param services services object
     * @return the measured-by term
     */
    public Term getMby(Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres, Services services);

    /**
     * Returns the contract in pretty HTML format.
     * @param services services instance
     * @return the html representation
     */
    public String getHTMLText(Services services);

    /**
     * Returns the contract in pretty plain text format.
     * @param services services instance
     * @return the plain text representation
     */
    public String getPlainText(Services services);

    /**
     * Tells whether, on saving a proof where this contract is available, the contract should be
     * saved too. (this is currently true for contracts specified directly in DL, but not for JML
     * contracts)
     * @return see above
     */
    public boolean toBeSaved();

    public boolean transactionApplicableContract();

    /**
     * Returns a parseable String representation of the contract. Precondition: toBeSaved() must be
     * true.
     * @param services the services instance
     * @return the (parseable) String representation
     */
    public String proofToString(Services services);

    /**
     * Returns a proof obligation to the passed initConfig.
     * @param initConfig the initial configuration
     * @return the proof obligation
     */
    public ContractPO createProofObl(InitConfig initConfig);

    /**
     * Lookup the proof obligation belonging to the contract in the specification repository.
     * @param services the services instance
     * @return the proof obligation according to the specification repository
     */
    public ProofOblInput getProofObl(Services services);

    /**
     * Returns a proof obligation to the passed contract and initConfig.
     * @param initConfig the initial configuration
     * @param contract the contract
     * @return the proof obligation
     */
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract);

    /**
     * Returns a proof obligation to the passed contract and initConfig.
     * @param initConfig the initial configuration
     * @param contract the contract
     * @param supportSymbolicExecutionAPI
     *              boolean saying whether symbolic execution api is supported
     * @return the proof obligation
     */
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract,
            boolean supportSymbolicExecutionAPI);

    /**
     * Returns a contract which is identical this contract except that the id is set to the new id.
     * @param newId the new id value
     * @return an identical contract with the new id
     */
    public Contract setID(int newId);

    /**
     * Returns a contract which is identical to this contract except that the KeYJavaType and
     * IObserverFunction are set to the new values.
     * @param newKJT the new KeYJavaType
     * @param newPM the new observer function
     * @return an identical contract with the new KJT and PM (see above)
     */
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM);

    /**
     * Returns technical name for the contract type.
     * @return the technical name
     */
    public String getTypeName();

    /**
     * Checks if a self variable is originally provided.
     *
     * @return {@code true} self variable is originally provided, {@code false} no self variable
     *         available.
     */
    public boolean hasSelfVar();

    @Override
    public Contract map(UnaryOperator<Term> op, Services services);

    /**
     * Class for storing the original variables without always distinguishing several different
     * cases depending on which variables are present/needed in order to provide a general
     * interface. At the moment only used for well-definedness checks (as those refer to already
     * existing structures).
     *
     * @author Michael Kirsten
     */
    final public class OriginalVariables {

        public final ProgramVariable self;
        public final ProgramVariable result;
        public final ProgramVariable exception;
        public final Map<LocationVariable, ProgramVariable> atPres;
        public final ImmutableList<ProgramVariable> params;

        /**
         * Create new instance of original variables
         * @param selfVar the original self variable
         * @param resVar the original result variable
         * @param excVar the original exception variable
         * @param atPreVars the original atPreVars
         * @param paramVars the original parameter variables
         */
        @SuppressWarnings("unchecked")
        public OriginalVariables(ProgramVariable selfVar, ProgramVariable resVar,
                ProgramVariable excVar,
                Map<? extends LocationVariable, ? extends ProgramVariable> atPreVars,
                ImmutableList<? extends ProgramVariable> paramVars) {
            this.self = selfVar;
            this.result = resVar;
            this.exception = excVar;
            this.atPres = (Map<LocationVariable, ProgramVariable>) atPreVars;
            if (paramVars == null) {
                this.params = ImmutableSLList.<ProgramVariable> nil();
            } else {
                this.params = (ImmutableList<ProgramVariable>) paramVars;
            }
        }

        /**
         * Adds a list of parameters and deletes the prior ones (if any).
         *
         * @param newParams
         * @return the changed original variables
         */
        public OriginalVariables add(ImmutableList<ProgramVariable> newParams) {
            return new OriginalVariables(self, result, exception, atPres, newParams);
        }
    }
}
