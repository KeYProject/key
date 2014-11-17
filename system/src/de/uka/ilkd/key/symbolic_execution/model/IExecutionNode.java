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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;

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
 * @author Martin Hentschel
 */
public interface IExecutionNode<S extends SourceElement> extends IExecutionElement {
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
   public IExecutionNode<?> getParent();
   
   /**
    * Returns the available children.
    * @return The available children.
    */
   public IExecutionNode<?>[] getChildren();
   
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
   public IExecutionNode<?>[] getCallStack();
   
   /**
    * Returns all available {@link IExecutionConstraint}s.
    * @return The available {@link IExecutionConstraint}s.
    */
   public IExecutionConstraint[] getConstraints();
   
   /**
    * Returns the active statement which is executed in the code.
    * @return The active statement which is executed in the code.
    */
   public S getActiveStatement();
   
   /**
    * Returns the {@link PositionInfo} of {@link #getActiveStatement()}.
    * @return The {@link PositionInfo} of {@link #getActiveStatement()}.
    */
   public PositionInfo getActivePositionInfo();
   
   /**
    * Returns the variable value pairs of the current state.
    * @return The variable value pairs.
    * @throws ProofInputException Occurred Exception.
    */
   public IExecutionVariable[] getVariables() throws ProofInputException;
   
   /**
    * Returns the variable value pairs of the current state under the given condition.
    * @param condition A {@link Term} specifying some additional constraints to consider.
    * @return The variable value pairs.
    */
   public IExecutionVariable[] getVariables(Term condition) throws ProofInputException;
   
   /**
    * Returns the number of memory layouts.
    * @return The number of memory layouts.
    * @throws ProofInputException Occurred Exception.
    */
   public int getLayoutsCount() throws ProofInputException;
   
   /**
    * Returns the equivalence classes of the memory layout with the given index.
    * @param layoutIndex The index of the memory layout.
    * @return The equivalence classes of the memory layout at the given index.
    * @throws ProofInputException Occurred Exception.
    */
   public ImmutableList<ISymbolicEquivalenceClass> getLayoutsEquivalenceClasses(int layoutIndex) throws ProofInputException;
   
   /**
    * Returns the initial memory layout before the method was executed.
    * @param layoutIndex The index of the memory layout.
    * @return The initial memory layout at the given index.
    * @throws ProofInputException Occurred Exception.
    */
   public ISymbolicLayout getInitialLayout(int layoutIndex) throws ProofInputException;
   
   /**
    * Returns the current memory layout which shows the memory
    * structure before the current node in the symbolic execution tree is executed.
    * @param layoutIndex The index of the memory layout.
    * @return The current memory layout at the given index.
    * @throws ProofInputException Occurred Exception.
    */
   public ISymbolicLayout getCurrentLayout(int layoutIndex) throws ProofInputException;
   
   /**
    * Returns all code blocks completed by this {@link IExecutionBlockStartNode}.
    * @return All code blocks completed by this {@link IExecutionBlockStartNode}.
    */
   public ImmutableList<IExecutionBlockStartNode<?>> getCompletedBlocks();
   
   /**
    * Returns the condition under which this node completes the code block of the given {@link IExecutionBlockStartNode}.
    * @param completedNode The completed {@link IExecutionBlockStartNode} for which the condition is requested.
    * @return The condition under which this node completes the code block of the given {@link IExecutionBlockStartNode}.
    */
   public Term getBlockCompletionCondition(IExecutionBlockStartNode<?> completedNode) throws ProofInputException;
   
   /**
    * Returns the human readable condition under which this node completes the code block of the given {@link IExecutionBlockStartNode}.
    * @param completedNode The completed {@link IExecutionBlockStartNode} for which the condition is requested.
    * @return The human readable condition under which this node completes the code block of the given {@link IExecutionBlockStartNode}.
    */
   public String getFormatedBlockCompletionCondition(IExecutionBlockStartNode<?> completedNode) throws ProofInputException;
}