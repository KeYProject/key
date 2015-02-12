package org.key_project.sed.core.model.memory;

import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;

/**
 * Defines the public methods to edit an {@link ISEDBaseMethodReturn} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEDMemoryBaseMethodReturn extends ISEDMemoryDebugNode, ISEDBaseMethodReturn {
   /**
    * Adds the given {@link IVariable} of the call state.
    * @param variable The {@link IVariable} of the call state to add.
    */
   public void addCallStateVariable(IVariable variable);
}
