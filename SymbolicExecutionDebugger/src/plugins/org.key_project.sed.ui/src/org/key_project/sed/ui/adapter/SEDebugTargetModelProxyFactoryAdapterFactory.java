package org.key_project.sed.ui.adapter;

import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IModelProxyFactory;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.ui.proxy.SEDebugTargetModelProxyFactory;

/**
 * This {@link IAdapterFactory} is used to return the special
 * {@link IModelProxyFactory} for {@link ISEDebugTarget}s.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDebugTargetModelProxyFactoryAdapterFactory implements IAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Object adaptableObject, Class adapterType) {
      if (IModelProxyFactory.class.equals(adapterType)) {
         return new SEDebugTargetModelProxyFactory();
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Class[] getAdapterList() {
      return new Class[] {IModelProxyFactory.class};
   }
}
