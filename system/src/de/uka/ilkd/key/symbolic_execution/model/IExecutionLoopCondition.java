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

package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionLoopCondition;

/**
 * <p>
 * A node in the symbolic execution tree which represents a loop condition,
 * e.g. {@code x >= 0}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionLoopCondition} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionLoopCondition
 */
public interface IExecutionLoopCondition extends IExecutionBlockStartNode<LoopStatement> {
   /**
    * Returns the loop expression which is executed.
    * @return The executed loop expression.
    */
   public Expression getGuardExpression();

   /**
    * Returns the code position of the executed loop expression ({@link #getGuardExpression()}).
    * @return The code of the executed loop expression.
    */
   public PositionInfo getGuardExpressionPositionInfo();
}