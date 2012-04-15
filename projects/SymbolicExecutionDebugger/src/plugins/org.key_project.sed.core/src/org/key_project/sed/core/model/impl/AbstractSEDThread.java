package org.key_project.sed.core.model.impl;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDThread}.
 * @author Martin Hentschel
 * @see ISEDThread
 */
public abstract class AbstractSEDThread extends AbstractSEDDebugNode implements ISEDThread {
   /**
    * The priority of this thread.
    */
   private int priority = 0;
   
   /**
    * The name of this thread.
    */
   private String name;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this thread is contained.
    */
   public AbstractSEDThread(ISEDDebugTarget target) {
      super(target, null, null);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDThread getThread() {
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
   public String getName() throws DebugException {
      return name;
   }

   /**
    * Sets the name of this thread.
    * @param name The name to set.
    */
   protected void setName(String name) {
      this.name = name;
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
      return getDebugTarget().canResume();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return getDebugTarget().canSuspend();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isSuspended() {
      return getDebugTarget().isSuspended();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      getDebugTarget().resume();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      getDebugTarget().suspend();
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
      return "Thread";
   }
}
