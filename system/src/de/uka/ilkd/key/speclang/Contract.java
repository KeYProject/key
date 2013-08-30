// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//


package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;


/**
 * A contractual agreement about an ObserverFunction.
 */
public interface Contract extends SpecificationElement {

    public static final int INVALID_ID = Integer.MIN_VALUE;


    /**
     * Returns the id number of the contract. If a contract has instances for
     * several methods (inheritance!), all instances have the same id.
     * The id is either non-negative or equal to INVALID_ID.
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
     * Returns the precondition of the contract.
     */
    public Term getPre(LocationVariable heap,
                       ProgramVariable selfVar,
	    	       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable,? extends ProgramVariable> atPreVars,
	    	       Services services);

    public Term getPre(List<LocationVariable> heapContext,
                       ProgramVariable selfVar,
	    	       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable,? extends ProgramVariable> atPreVars,
	    	       Services services);

    /**
     * Returns the precondition of the contract.
     */
    public Term getPre(LocationVariable heap,
                       Term heapTerm,
	               Term selfTerm,
	    	       ImmutableList<Term> paramTerms,
                       Map<LocationVariable,Term> atPres,
	    	       Services services);

    public Term getPre(List<LocationVariable> heapContext,
                       Map<LocationVariable,Term> heapTerms,
	               Term selfTerm,
	    	       ImmutableList<Term> paramTerms,
                       Map<LocationVariable,Term> atPres,
	    	       Services services);


    public Term getGlobalDefs(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Services services);

    /**
     * Returns the measured_by clause of the contract.
     */
    public Term getMby(ProgramVariable selfVar,
	               ImmutableList<ProgramVariable> paramVars,
	               Services services);

    /**
     * Returns the measured_by clause of the contract.
     */
    public Term getMby(Map<LocationVariable,Term> heapTerms,
	               Term selfTerm,
	               ImmutableList<Term> paramTerms,
                   Map<LocationVariable, Term> atPres,
	               Services services);

    /**
     * Returns the contract in pretty HTML format.
     */
    public String getHTMLText(Services services);

    /**
     * Returns the contract in pretty plain text format.
     */
    public String getPlainText(Services services);

    /**
     * Tells whether, on saving a proof where this contract is available, the
     * contract should be saved too. (this is currently true for contracts
     * specified directly in DL, but not for JML contracts)
     */
    public boolean toBeSaved();

    public boolean transactionApplicableContract();

    /**
     * Returns a parseable String representation of the contract.
     * Precondition: toBeSaved() must be true.
     */
    public String proofToString(Services services);


    /**
     * Returns a proof obligation to the passed contract and initConfig.
     */
    public ProofOblInput createProofObl(InitConfig initConfig,
	    Contract contract);

    /**
     * Returns a contract which is identical this contract except that
     * the id is set to the new id.
     */
    public Contract setID(int newId);


    /**
     * Returns a contract which is identical this contract except that
     * the KeYJavaType and IObserverFunction are set to the new values.
     */
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM);


    /**
     * Returns technical name for the contract type.
     */
    public String getTypeName();
    
    /**
     * Checks if a self variable is originally provided.
     * @return {@code true} self variable is originally provided, {@code false} no self variable available.
     */
    public boolean hasSelfVar();
}
