package org.key_project.sed.core.adapter;

import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.provider.SEDDebugNodeContentProvider;

/**
 * Provides the default provider for {@link ISEDDebugElement}s.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDDebugNodeAdapterFactory implements IAdapterFactory {
   /**
    * The singleton instance which is always returned in {@link #getAdapter(Object, Class)} for {@link IElementContentProvider}.
    */
   private SEDDebugNodeContentProvider nodeProvider;
   
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Object adaptableObject, Class adapterType) {
      if (IElementContentProvider.class.equals(adapterType)) {
         if (adaptableObject instanceof ISEDDebugNode &&
               IElementContentProvider.class.equals(adapterType)) {
              if (nodeProvider == null) {
                 nodeProvider = new SEDDebugNodeContentProvider();
              }
              return nodeProvider;
           }
           else {
              return null;
           }
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
      return new Class[] {IElementContentProvider.class};
   }
}
