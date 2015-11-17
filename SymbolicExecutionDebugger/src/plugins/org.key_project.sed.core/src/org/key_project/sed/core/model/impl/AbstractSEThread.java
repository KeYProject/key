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

package org.key_project.sed.core.model.impl;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.sourcesummary.ISESourceModel;
import org.key_project.sed.core.util.ISEIterator;
import org.key_project.sed.core.util.SEBreadthFirstIterator;
import org.key_project.util.java.ArrayUtil;

/**
 * Provides a basic implementation of {@link ISEThread}.
 * @author Martin Hentschel
 * @see ISEThread
 */
public abstract class AbstractSEThread extends AbstractSEStackFrameCompatibleDebugNode implements ISEThread {
   /**
    * Is this {@link ISEThread} executable meaning that
    * suspend, resume, step operations and disconnect are supported?;
    */
   private final boolean executable;
   
   /**
    * The priority of this thread.
    */
   private int priority = 0;

   /**
    * Indicates that the process is currently suspended or not.
    */
   private boolean suspended = true;
   
   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this thread is contained.
    * @param executable {@code true} Support suspend, resume, etc.; {@code false} Do not support suspend, resume, etc.
    */
   public AbstractSEThread(ISEDebugTarget target, boolean executable) {
      super(target, null, null);
      this.executable = executable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEThread getThread() {
      return this;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getPriority() throws DebugException {
      return priority;
   }

   /**
    * Sets the priortiy of this thread.
    * @param priority The priortiy to set.
    */
   protected void setPriority(int priority) {
      this.priority = priority;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IStackFrame[] getStackFrames() throws DebugException {
      return new IStackFrame[0];
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasStackFrames() throws DebugException {
      IStackFrame[] frames = getStackFrames();
      return frames != null && frames.length >= 1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IStackFrame getTopStackFrame() throws DebugException {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IBreakpoint[] getBreakpoints() {
      return new IBreakpoint[0];
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return executable && isSuspended() && !isTerminated() && !getDebugTarget().isDisconnected();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return executable && !isSuspended() && !isTerminated() && !getDebugTarget().isDisconnected();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isSuspended() {
      return suspended;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      suspended = false;
      fireResumeEvent(DebugEvent.CLIENT_REQUEST);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      ISESourceModel sourceModel = getDebugTarget().getSourceModel();
      if (sourceModel != null) {
         sourceModel.setPossiblyIncomplete();
      }
      suspended = true;
      fireSuspendEvent(DebugEvent.CLIENT_REQUEST);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepInto() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepOver() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStepReturn() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isStepping() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepInto() throws DebugException {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepOver() throws DebugException {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stepReturn() throws DebugException {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canTerminate() {
      return getDebugTarget().canTerminate();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isTerminated() {
      return getDebugTarget().isTerminated();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      getDebugTarget().terminate();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      try {
         return getName();
      }
      catch (DebugException e) {
         return e.getMessage();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNodeType() {
      return "Start";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ISENode[] getLeafsToSelect() throws DebugException {
      return collectLeafs(this);
   }
   
   /**
    * Collects all leaf nodes starting at the given node. If at some leafs
    * breakpoints are hit only nodes were breakpoints are hit are returned.
    * @param start The {@link ISENode} to start at.
    * @return The found leafs.
    * @throws DebugException Occurred Exception.
    */
   protected ISENode[] collectLeafs(ISENode start) throws DebugException {
      List<ISENode> leafs = new LinkedList<ISENode>();
      List<ISENode> leafsWithBreakpointHit = new LinkedList<ISENode>();
      ISEIterator iter = new SEBreadthFirstIterator(start);
      while (iter.hasNext()) {
         ISEDebugElement next = iter.next();
         if (next instanceof ISENode) {
            ISENode node = (ISENode)next;
            if (ArrayUtil.isEmpty(node.getChildren())) {
               leafs.add(node);
               if (!ArrayUtil.isEmpty(node.computeHitBreakpoints())) {
                  leafsWithBreakpointHit.add(node);
               }
            }
         }
      }
      if (!leafsWithBreakpointHit.isEmpty()) {
         return leafsWithBreakpointHit.toArray(new ISENode[leafsWithBreakpointHit.size()]);
      }
      else {
         return leafs.toArray(new ISENode[leafs.size()]);
      }
   }
}