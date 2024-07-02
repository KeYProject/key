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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public interface OperationContract extends Contract {

    @Override
    public IProgramMethod getTarget();

    @Override
    public OperationContract map(UnaryOperator<Term> op, Services services);

    /**
     * Returns <code>true</code> iff the method (according to the contract) does
     * not modify the heap at all, i.e., iff it is "strictly pure."
     *
     * @return whether this contract is strictly pure.
     */
    public boolean hasModifiesClause(LocationVariable heap);

    /**
     * Returns the modifies clause of the contract.
     *
     * @param heapVar   the heap variable.
     * @param selfVar   the self variable.
     * @param paramVars the list of parameter variables.
     * @param services  the services object.
     * @return the modifies clause.
     */
    public Term getMod(LocationVariable heapVar, ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services);

    /**
     * Returns the modifies clause of the contract.
     *
     * @param heapVar    the heap variable
     * @param heapTerm   the heap variable term.
     * @param selfTerm   the self variable term.
     * @param paramTerms the list of parameter variable terms.
     * @param services   the services object.
     * @return the modifies clause.
     */
    public Term getMod(LocationVariable heapVar, Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services);

    public Term getFreePre(LocationVariable heap,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           Map<LocationVariable,? extends ProgramVariable> atPreVars,
                           Services services);

    public Term getFreePre(List<LocationVariable> heapContext,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           Map<LocationVariable,? extends ProgramVariable> atPreVars,
                           Services services);

    public Term getFreePre(LocationVariable heap,
                           Term heapTerm,
                           Term selfTerm,
                           ImmutableList<Term> paramTerms,
                           Map<LocationVariable,Term> atPres,
                           Services services);
}