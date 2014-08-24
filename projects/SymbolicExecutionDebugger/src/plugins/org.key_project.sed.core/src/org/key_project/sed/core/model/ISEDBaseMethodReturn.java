package org.key_project.sed.core.model;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;

/**
 * Defines the basic functionality of {@link ISEDMethodReturn} and {@link ISEDExceptionalMethodReturn}.
 * @author Martin Hentschel
 */
public interface ISEDBaseMethodReturn extends ISEDDebugNode, IStackFrame {
   /**
    * Returns the condition under which the calling {@link ISEDMethodCall} is returned in this state.
    * @return
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDBranchCondition getMethodReturnCondition() throws DebugException;
}
