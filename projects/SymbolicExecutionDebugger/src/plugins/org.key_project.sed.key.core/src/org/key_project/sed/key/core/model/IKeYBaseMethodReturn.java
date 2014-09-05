package org.key_project.sed.key.core.model;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;

public interface IKeYBaseMethodReturn {
   /**
    * Returns the method call node if available in debug model.
    * @return The {@link KeYMethodCall} node or {@code null} if not available.
    */
   public KeYMethodCall getMethodCall();
   
   public IExecutionBaseMethodReturn<?> getExecutionNode();
   
   public SEDMemoryBranchCondition getMethodReturnCondition() throws DebugException;
}
