package org.key_project.sed.core.model;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IVariable;

/**
 * Defines the basic functionality of {@link ISEMethodReturn} and {@link ISEExceptionalMethodReturn}.
 * @author Martin Hentschel
 */
public interface ISEBaseMethodReturn extends ISENode, IStackFrame {
   /**
    * Returns the condition under which the calling {@link ISEMethodCall} is returned in this state.
    * @return
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEBranchCondition getMethodReturnCondition() throws DebugException;
   
   /**
    * Returns the variable value pairs of the state when the method has been called.
    * @return The variable value pairs.
    * @throws DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public IVariable[] getCallStateVariables() throws DebugException;
}
