/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.infflow;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.ImmutableList;



/**
 * A contract about the dependencies of an observer symbol, consisting of a precondition, a depends
 * clause, and a measured-by clause.
 */
public interface InformationFlowContract extends Contract {

    String getBaseName();


    @Override
    IProgramMethod getTarget();


    KeYJavaType getSpecifiedIn();


    /**
     * Returns <code>true</code> iff the method (according to the contract) does not modify the heap
     * at all, i.e., iff it is "strictly pure."
     *
     * @return whether this contract is strictly pure.
     */
    boolean hasModifiableClause();


    /**
     * Returns the original precondition of the contract.
     */
    JTerm getPre();


    /**
     * Returns the original free precondition of the contract.
     *
     * @return the original free precondition
     */
    JTerm getFreePre();


    /**
     * Returns the original modifiable clause of the contract.
     */
    JTerm getModifiable();


    /**
     * Returns the original measured_by clause of the contract.
     */
    @Override
    JTerm getMby();


    /**
     * Get the exception-variable which is used in this contract.
     *
     * @return used exception-variable
     */
    JTerm getExc();

    JTerm getAtPre();


    boolean isReadOnlyContract();


    /**
     * Returns the modality of the contract.
     */
    JModality.JavaModalityKind getModalityKind();


    InformationFlowContract setName(String name);


    InformationFlowContract setModality(JModality.JavaModalityKind modalityKind);


    InformationFlowContract setModifiable(JTerm modifiable);


    /**
     * Return a new contract which equals this contract except that the id is set to the new id.
     */
    @Override
    InformationFlowContract setID(int newId);


    /**
     * Get the self-variable which is used in this contract.
     *
     * @return originally used self-variable
     */
    JTerm getSelf();


    /**
     * Get the parameter-variables which is used in this contract.
     *
     * @return originally used parameter-variables
     */
    ImmutableList<JTerm> getParams();


    /**
     * Return a new contract which equals this contract except that the the KeYJavaType and
     * ObserverFunction are set to the new values.
     */
    @Override
    InformationFlowContract setTarget(KeYJavaType newKJT, IObserverFunction newPM);


    /**
     * Get the result-variable which is used in this contract.
     *
     * @return used result-variable
     */
    JTerm getResult();


    boolean equals(Contract c);


    /**
     * For generating contract name of SymbolicExecutionPO
     *
     * @return String "Method Contract"
     */
    String getPODisplayName();


    /**
     * Returns the dependency set of the contract.
     */
    JTerm getDep();


    /**
     * Returns the set of views.
     */
    ImmutableList<InfFlowSpec> getInfFlowSpecs();


    boolean hasInfFlowSpec();

    @Override
    InformationFlowContract map(UnaryOperator<JTerm> op, Services services);
}
