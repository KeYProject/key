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

import java.util.function.UnaryOperator;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.util.InfFlowSpec;



/**
 * A contract about the dependencies of an observer symbol, consisting of
 * a precondition, a depends clause, and a measured-by clause.
 */
public interface InformationFlowContract extends Contract {

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
     * Returns the original precondition of the contract.
     */
    Term getPre();


    /**
     * Returns the original free precondition of the contract.
     *
     * @return the original free precondition
     */
    Term getFreePre();


    /**
     * Returns the original modifies clause of the contract.
     */
    Term getMod();


    /**
     * Returns the original measured_by clause of the contract.
     */
    @Override
    Term getMby();


    /**
     * Get the exception-variable which is used in this contract.
     * @return used exception-variable
     */
    public Term getExc();

    public Term getAtPre();


    public boolean isReadOnlyContract();


    /**
     * Returns the modality of the contract.
     */
    public Modality getModality();


    public InformationFlowContract setName(String name);


    public InformationFlowContract setModality(Modality modality);


    public InformationFlowContract setModifies(Term modifies);


    /**
     * Return a new contract which equals this contract except that the id is
     * set to the new id.
     */
    @Override
    public InformationFlowContract setID(int newId);


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
    public InformationFlowContract setTarget(KeYJavaType newKJT,
                                             IObserverFunction newPM);


    /**
     * Get the result-variable which is used in this contract.
     * @return used result-variable
     */
    Term getResult();


    public boolean equals(Contract c);


    /**
     * For generating contract name of SymbolicExecutionPO
     * @return String "Method Contract"
     */
    public String getPODisplayName();


    /**
     * Returns the dependency set of the contract.
     */
    Term getDep();


    /**
     * Returns the set of views.
     */
    ImmutableList<InfFlowSpec> getInfFlowSpecs();


    public boolean hasInfFlowSpec();

    @Override
    public InformationFlowContract map(UnaryOperator<Term> op, Services services);
}
