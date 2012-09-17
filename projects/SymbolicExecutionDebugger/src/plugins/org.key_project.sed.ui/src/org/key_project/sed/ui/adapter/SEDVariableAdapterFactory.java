package org.key_project.sed.ui.adapter;

import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.debug.internal.ui.model.elements.VariableLabelProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementLabelProvider;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.ui.provider.SEDVariableLabelProvider;

/**
 * This {@link IAdapterFactory} is used to return the special
 * {@link VariableLabelProvider} for {@link ISEDVariable} and {@link ISEDValue}s. 
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDVariableAdapterFactory implements IAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Object adaptableObject, Class adapterType) {
      if (IElementLabelProvider.class.equals(adapterType)) {
         if (adaptableObject instanceof ISEDVariable) {
            return new SEDVariableLabelProvider();
         }
         else {
            return new VariableLabelProvider();
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
      return new Class[] {IElementLabelProvider.class};
   }
}
