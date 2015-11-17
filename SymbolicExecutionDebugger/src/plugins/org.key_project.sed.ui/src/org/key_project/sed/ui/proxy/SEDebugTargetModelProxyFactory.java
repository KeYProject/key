package org.key_project.sed.ui.proxy;

import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelProxy;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelProxyFactory;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.key_project.sed.core.model.ISEDebugTarget;

/**
 * An {@link IModelProxyFactory} which creates {@link SEDebugTargetProxy} instances.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDebugTargetModelProxyFactory implements IModelProxyFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public IModelProxy createModelProxy(Object element, IPresentationContext context) {
      if (IDebugUIConstants.ID_DEBUG_VIEW.equals(context.getId())) {
         if (element instanceof IDebugTarget) {
            return new SEDebugTargetProxy((ISEDebugTarget)element);
         }
      }
      return null;
   }
}
