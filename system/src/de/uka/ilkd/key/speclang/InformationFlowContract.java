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
import de.uka.ilkd.key.logic.op.Modality;



/**
 * A contract about the dependencies of an observer symbol, consisting of 
 * a precondition, a depends clause, and a measured-by clause.
 */
public interface InformationFlowContract extends SymbolicExecData {

    /**
     * Returns the dependency set of the contract.
     */
    public Term getDep(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services);


    Term getDep();


    public ImmutableList<ImmutableList<Term>> getRespects(Term heapTerm,
                                           Term selfTerm,
                                           ImmutableList<Term> paramTerms,
                                           Term resultTerm,
                                           Services services);


    ImmutableList<ImmutableList<Term>> getRespects();


    /**
     * Returns the declassification formulas.
     */
    public ImmutableList<ImmutableList<Term>> getDeclassifies(
            Term heapTerm,
            Term selfTerm,
            ImmutableList<Term> paramTerms,
            Term resultTerm,
            Services services);


    public ImmutableList<ImmutableList<Term>> getDeclassifies();


    public boolean hasDeclassifies();


    public boolean hasRespects();


    @Override
    public InformationFlowContract andPre(Term pre,
                                          Term usedSelf,
                                          ImmutableList<Term> usedParams,
                                          Services services);


    @Override
    public InformationFlowContract orPre(Term pre,
                                         Term usedSelf,
                                         ImmutableList<Term> usedParams,
                                         Services services);


    @Override
    public InformationFlowContract addMby(Term condition,
                                          Term mby);


    @Override
    public InformationFlowContract addMod(Term mod,
                                          Services services);


    @Override
    public InformationFlowContract setName(String name);


    @Override
    public InformationFlowContract setModality(Modality modality);


    @Override
    public InformationFlowContract setModifies(Term modifies);


    public SymbolicExecData getSymbExecData(Services services);


    /**
     * Return a new contract which equals this contract except that the id is
     * set to the new id.
     */
    @Override
    public InformationFlowContract setID(int newId);


    /**
     * Return a new contract which equals this contract except that the
     * the KeYJavaType and ObserverFunction are set to the new values.
     */
    @Override
    public InformationFlowContract setTarget(KeYJavaType newKJT,
                                             IObserverFunction newPM);
    
}
