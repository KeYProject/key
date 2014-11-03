/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.core.model.memory;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDConstraint;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDMethodReturn;

/**
 * Implementation of {@link ISEDMethodReturn} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryMethodReturn extends AbstractSEDMethodReturn implements ISEDMemoryStackFrameCompatibleDebugNode, ISEDMemoryBaseMethodReturn {
   /**
    * The contained child nodes.
    */
   private final List<ISEDDebugNode> children = new LinkedList<ISEDDebugNode>();
   
   /**
    * The contained variables.
    */
   private final List<IVariable> variables = new LinkedList<IVariable>();
   
   /**
    * The contained variables at the call state.
    */
   private final List<IVariable> callStateVariables = new LinkedList<IVariable>();
   
   /**
    * The name of this debug node.
    */
   private String name;
   
   /**
    * The human readable path condition to this node.
    */
   private String pathCondition;
   
   /**
    * The source path.
    */
   private String sourcePath;

   /**
    * The line number.
    */
   private int lineNumber = -1;

   /**
    * The index of the start character.
    */
   private int charStart = -1;
   
   /**
    * The index of the end character.
    */
   private int charEnd = -1;

   /**
    * The method call stack.
    */
   private ISEDDebugNode[] callStack;

   /**
    * The method return condition.
    */
   private ISEDBranchCondition methodReturnCondition;
   
   /**
    * The contained {@link ISEDConstraint}s.
    */
   private final List<ISEDConstraint> constraints = new LinkedList<ISEDConstraint>();
   
   /**
    * The known group start conditions.
    */
   private final List<ISEDBranchCondition> groupStartConditions = new LinkedList<ISEDBranchCondition>();
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this method return is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this method return is contained.
    */
   public SEDMemoryMethodReturn(ISEDDebugTarget target, 
                                ISEDDebugNode parent, 
                                ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      return name;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getSourcePath() {
      return sourcePath;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public int getLineNumber() throws DebugException {
      return lineNumber;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharStart() throws DebugException {
      return charStart;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharEnd() throws DebugException {
      return charEnd;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode[] getChildren() throws DebugException {
      return children.toArray(new ISEDDebugNode[children.size()]);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addChild(ISEDDebugNode child) {
      if (child != null) {
         children.add(child);
      }
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public void removeChild(ISEDDebugNode child) {
      if (child != null) {
         children.remove(child);
      }
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public void addChild(int index, ISEDDebugNode child) {
      if (child != null) {
         children.add(index, child);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int indexOfChild(ISEDDebugNode child) {
      if (child != null) {
         return children.indexOf(child);
      }
      else {
         return -1;
      }
   }
   
   /**
    * Sets the name of this node.
    * @param name the name to set.
    */
   public void setName(String name) {
      this.name = name;
   }

   /**
    * Sets the line number.
    * @param lineNumber The line number or {@code -1} if it is unknown.
    */
   public void setLineNumber(int lineNumber) {
      this.lineNumber = lineNumber;
   }

   /**
    * Sets the index of the start character.
    * @param charStart The index or {@code -1} if it is unknown.
    */
   public void setCharStart(int charStart) {
      this.charStart = charStart;
   }

   /**
    * Sets the index of the end character.
    * @param charEnd The index or {@code -1} if it is unknown.
    */
   public void setCharEnd(int charEnd) {
      this.charEnd = charEnd;
   }
   
   /**
    * Sets the source path.
    * @param sourcePath The source path to set.
    */
   public void setSourcePath(String sourcePath) {
      this.sourcePath = sourcePath;
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setId(String id) {
      super.setId(id);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addVariable(IVariable variable) {
      variables.add(variable);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IVariable[] getVariables() throws DebugException {
      return variables.toArray(new IVariable[variables.size()]);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addCallStateVariable(IVariable variable) {
      callStateVariables.add(variable);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IVariable[] getCallStateVariables() throws DebugException {
      return callStateVariables.toArray(new IVariable[callStateVariables.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getPathCondition() throws DebugException {
      return pathCondition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setPathCondition(String pathCondition) {
      this.pathCondition = pathCondition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode[] getCallStack() throws DebugException {
      return callStack;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setCallStack(ISEDDebugNode[] callStack) {
      this.callStack = callStack;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDBranchCondition getMethodReturnCondition() throws DebugException {
      return methodReturnCondition;
   }

   /**
    * Sets the method return condition.
    * @param methodReturnCondition The method return condition to set.
    */
   public void setMethodReturnCondition(ISEDBranchCondition methodReturnCondition) {
      this.methodReturnCondition = methodReturnCondition;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addConstraint(ISEDConstraint constraint) {
      if (constraint != null) {
         constraints.add(constraint);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDConstraint[] getConstraints() throws DebugException {
      return constraints.toArray(new ISEDConstraint[constraints.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDBranchCondition[] getGroupStartConditions() throws DebugException {
      return groupStartConditions.toArray(new ISEDBranchCondition[groupStartConditions.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addGroupStartCondition(ISEDBranchCondition groupStartCondition) {
      if (groupStartCondition != null) {
         groupStartConditions.add(groupStartCondition);
      }
   }
}