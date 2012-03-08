package org.key_project.sed.core.model.impl;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IRegisterGroup;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDDebugNode}s which
 * also realize the interface {@link IStackFrame} for compatibility reasons
 * with the Eclipse debug API.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDStackFrameCompatibleDebugNode extends AbstractSEDDebugNode implements IStackFrame {
   /**
    * The {@link ISEDThread} in that this node is contained.
    */
   private ISEDThread thread;
   
   /**
    * The name of this debug node.
    */
   private String name;
   
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
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this node is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    */
   public AbstractSEDStackFrameCompatibleDebugNode(ISEDDebugTarget target,
                                                   ISEDDebugNode parent, 
                                                   ISEDThread thread) {
      super(target, parent);
      this.thread = thread;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDThread getThread() {
      return thread;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IVariable[] getVariables() throws DebugException {
      return new IVariable[0];
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasVariables() throws DebugException {
      IVariable[] variables = getVariables();
      return variables != null && variables.length >= 1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IRegisterGroup[] getRegisterGroups() throws DebugException {
      return new IRegisterGroup[0];
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasRegisterGroups() throws DebugException {
      IRegisterGroup[] registerGroups = getRegisterGroups();
      return registerGroups != null && registerGroups.length >= 1;
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
   public String getName() throws DebugException {
      return name;
   }

   /**
    * Sets the name of this node.
    * @param name the name to set.
    */
   protected void setName(String name) {
      this.name = name;
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
    * Sets the line number.
    * @param lineNumber The line number or {@code -1} if it is unknown.
    */
   protected void setLineNumber(int lineNumber) {
      this.lineNumber = lineNumber;
   }

   /**
    * Sets the index of the start character.
    * @param charStart The index or {@code -1} if it is unknown.
    */
   protected void setCharStart(int charStart) {
      this.charStart = charStart;
   }

   /**
    * Sets the index of the end character.
    * @param charEnd The index or {@code -1} if it is unknown.
    */
   protected void setCharEnd(int charEnd) {
      this.charEnd = charEnd;
   }
}
