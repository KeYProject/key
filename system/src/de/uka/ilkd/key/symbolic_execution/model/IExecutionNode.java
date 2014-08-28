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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;

/**
 * <p>
 * Provides the basic methods each node in a symbolic execution tree
 * should have and allows to access the children. A symbolic execution tree
 * always starts with an {@link IExecutionStart} and is created via
 * a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * <p>
 * The following concrete nodes are available
 * <ul>
 * <li>{@link IExecutionStart} (root node)</li>
 * <li>{@link IExecutionStatement} (single statement, e.g. {@code int x =  1 + 2;})</li>
 * <li>{@link IExecutionBranchStatement} (branch statement, e.g. {@code if(x >= 0)})</li>
 * <li>{@link IExecutionBranchCondition} (branch condition, e.g. {@code x < 0})</li>
 * <li>{@link IExecutionMethodCall} (method call, e.g. {@code foo()})</li>
 * <li>{@link IExecutionMethodReturn} (method return, e.g. {@code return 42})</li>
 * <li>{@link IExecutionTermination} (termination, e.g. {@code <end>} or {@code <uncaught java.lang.NullPointerException>})</li>
 * </ul>
 * </p>
 * <p>
 * Nodes which represents a statement of the code and have a state are
 * sub interfaces of sub interface {@link IExecutionStateNode}.
 * </p>
 * @author Martin Hentschel
 */
public interface IExecutionNode extends IExecutionElement {
   /**
    * Prefix that is used in {@link IExecutionNode}s which represents an internal state in KeY which is not part of the source code.
    */
   public static final String INTERNAL_NODE_NAME_START = "<";

   /**
    * Suffix that is used in {@link IExecutionNode}s which represents an internal state in KeY which is not part of the source code.
    */
   public static final String INTERNAL_NODE_NAME_END = ">";
   
   /**
    * Returns the parent {@link IExecutionNode} or {@code null} if the
    * current node is the root.
    * @return The parent {@link IExecutionNode} or {@code null} on root.
    */
   public IExecutionNode getParent();
   
   /**
    * Returns the available children.
    * @return The available children.
    */
   public IExecutionNode[] getChildren();
   
   /**
    * Checks if this node has changed the path condition of the parent.
    * @return {@code true} has different path condition compared to its parent, {@code false} has same path condition as parent.
    */
   public boolean isPathConditionChanged();
   
   /**
    * Returns the path condition to reach this node as {@link Term}.
    * @return The path condition to reach this node as {@link Term}.
    */
   public Term getPathCondition() throws ProofInputException;
   
   /**
    * Returns the human readable path condition to reach this node as string. 
    * @return The human readable path condition as string.
    */
   public String getFormatedPathCondition() throws ProofInputException;
   
   /**
    * Returns the method call stack.
    * @return The method call stack. 
    */
   public IExecutionNode[] getCallStack();
   
   /**
    * Returns all available {@link IExecutionConstraint}s.
    * @return The available {@link IExecutionConstraint}s.
    */
   public IExecutionConstraint[] getConstraints();
}