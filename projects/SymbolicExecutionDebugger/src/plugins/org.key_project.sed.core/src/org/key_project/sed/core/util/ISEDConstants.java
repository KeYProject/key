package org.key_project.sed.core.util;

import org.eclipse.debug.internal.ui.viewers.model.provisional.PresentationContext;
import org.eclipse.debug.internal.ui.viewers.model.provisional.TreeModelViewer;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Provides Symbolic Execution Debugger (SED) specific constants.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public interface ISEDConstants {
   /**
    * The ID used for the call stack, accessible via {@link ISEDDebugNode#getCallStack()}.
    */
   public static final String ID_CALL_STACK = "org.key_project.sed.core.callStack";
   
   /**
    * Property key used in {@link PresentationContext} to define the input of the {@link TreeModelViewer} in which the {@link PresentationContext} is used.
    */
   public static final String PRESENTATION_CONTEXT_PROPERTY_INPUT = "org.key_project.sed.core.input";
}
