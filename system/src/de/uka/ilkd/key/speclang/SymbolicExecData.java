// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;



public interface SymbolicExecData extends Contract {
    
    public String getBaseName();

    
    @Override
    public IProgramMethod getTarget();
    
    
    public KeYJavaType getSpecifiedIn();
    

    /**
     * Returns <code>true</code> iff the method (according to the contract) does
     * not modify the heap at all, i.e., iff it is "strictly pure."
     * 
     * @return whether this contract is strictly pure.
     */
    public boolean hasModifiesClause();
    
    
    /**
     * Returns the precondition of the contract. Not applicable for transactions.
     */
    public Term getPre(Term heapTerm,
                       Term selfTerm, 
                       ImmutableList<Term> paramTerms,
                       Services services);    

    
    /**
     * Returns the original precondition of the contract.
     */
    Term getPre();
    
    /**
     * Returns the modifies clause of the contract.
     */
    public Term getMod(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services);
    
    /**
     * Returns the original modifies clause of the contract.
     */
    Term getMod();


    /**
     * Returns the original measured_by clause of the contract.
     */
    Term getMby();

    
    /**
     * Get the exception-variable which is used in this contract.
     * @return used exception-variable
     */
    public Term getExc();


    

    public SymbolicExecData andPre(Term pre,
                                   Term usedSelf,
                                   ImmutableList<Term> usedParams,
                                   Services services);


    public SymbolicExecData orPre(Term pre,
                                  Term usedSelf,
                                  ImmutableList<Term> usedParams,
                                  Services services);


    public boolean isReadOnlyContract();


    /**
     * Returns the modality of the contract.
     */
    public Modality getModality();
    
    
    public Modality getPOModality();


    public SymbolicExecData addMby(Term condition,
                                    Term mby);


    /**
     * Combine passed modifies-clause with the contract.
     * @param mod           additional modifies-clause
     * @param services      the service object
     * @return              a new contract with the combined modifies-clause.
     */
    public SymbolicExecData addMod(Term mod,
                       Services services);
    

    public SymbolicExecData setName(String name);


    public SymbolicExecData setModality(Modality modality);


    public SymbolicExecData setModifies(Term modifies);


    /**
     * Return a new contract which equals this contract except that the id is
     * set to the new id.
     */
    @Override
    public SymbolicExecData setID(int newId);

    
    /**
     * Get the self-variable which is used in this contract.
     * @return originally used self-variable
     */
    Term getSelf();


    /**
     * Get the parameter-variables which is used in this contract.
     * @return originally used parameter-variables
     */
    ImmutableList<Term> getParams();


    /**
     * Return a new contract which equals this contract except that the
     * the KeYJavaType and ObserverFunction are set to the new values.
     */
    @Override
    public SymbolicExecData setTarget(KeYJavaType newKJT,
                                      IObserverFunction newPM);


    /**
     * Get the result-variable which is used in this contract.
     * @return used result-variable
     */
    Term getResult();
    
    
    public boolean equals(Contract c);
    
    public boolean equalsData(SymbolicExecData data);
    
}
