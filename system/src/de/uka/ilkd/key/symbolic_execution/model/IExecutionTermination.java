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

package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionTermination;

/**
 * <p>
 * A node in the symbolic execution tree which represents the normal termination of a branch,
 * e.g. {@code <end>} in case of normal termination or {@code <uncaught java.lang.NullPointerException>}
 * in case of exceptional termination.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionTermination} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionTermination
 */
public interface IExecutionTermination extends IExecutionNode {
   /**
    * The default name of a termination node.
    */
   public static final String DEFAULT_TERMINATION_NODE_NAME = INTERNAL_NODE_NAME_START + "end" + INTERNAL_NODE_NAME_END;

   /**
    * Returns the {@link IProgramVariable} which is used in the {@link Sequent}
    * of {@link Proof#root()} to check if a normal or exceptional termination
    * occurred.
    * @return The {@link IProgramVariable} which is used to caught global exceptions.
    */
   public IProgramVariable getExceptionVariable();
   
   /**
    * Returns the {@link Sort} of the caught exception.
    * @return The {@link Sort} of the caught exception.
    */
   public Sort getExceptionSort();
   
   /**
    * Checks if a normal or an exceptional termination occurred.
    * @return {@code true} exceptional termination, {@code false} normal termination.
    */
   public boolean isExceptionalTermination();
}