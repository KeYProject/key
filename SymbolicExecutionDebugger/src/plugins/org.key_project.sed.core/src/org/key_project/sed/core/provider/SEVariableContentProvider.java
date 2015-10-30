package org.key_project.sed.core.provider;

import org.eclipse.debug.internal.ui.model.elements.VariableContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.key_project.sed.core.util.ISEConstants;

/**
 * Extended {@link VariableContentProvider} to support also {@link ISEConstants#ID_CALL_STATE}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEVariableContentProvider extends VariableContentProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean supportsContext(IPresentationContext context) {
      return ISEConstants.ID_CALL_STATE.equals(context.getId()) || super.supportsContext(context);
   }
}
