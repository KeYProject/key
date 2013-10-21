/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISEDLoopInvariant;
import org.key_project.sed.core.model.impl.AbstractSEDLoopInvariant;

/**
 * Implementation of {@link ISEDLoopInvariant} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryLoopInvariant extends AbstractSEDLoopInvariant implements ISEDMemoryStackFrameCompatibleDebugNode, ISEDMemoryDebugNode {
   /**
    * The contained child nodes.
    */
   private List<ISEDDebugNode> children = new LinkedList<ISEDDebugNode>();
   
   /**
    * The contained variables.
    */
   private List<IVariable> variables = new LinkedList<IVariable>();
   
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
    * Initially valid?
    */
   private boolean initiallyValid;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this loop invariant is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this loop invariant is contained.
    */
   public SEDMemoryLoopInvariant(ISEDDebugTarget target, 
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
   public boolean isInitiallyValid() {
      return initiallyValid;
   }

   /**
    * Sets the initially valid flag.
    * @param initiallyValid The initially valid flag to set.
    */
   public void setInitiallyValid(boolean initiallyValid) {
      this.initiallyValid = initiallyValid;
   }
}