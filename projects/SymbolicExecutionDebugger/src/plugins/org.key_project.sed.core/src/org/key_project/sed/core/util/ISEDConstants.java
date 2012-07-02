package org.key_project.sed.core.util;

import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Provides Symbolic Execution Debugger (SED) specific constants.
 * @author Martin Hentschel
 */
public interface ISEDConstants {
   /**
    * The ID used for the call stack, accessible via {@link ISEDDebugNode#getCallStack()}.
    */
   public static final String ID_CALL_STACK = "org.key_project.sed.core.callStack";
}
