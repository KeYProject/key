package org.key_project.sed.core.provider;

import org.eclipse.debug.internal.ui.elements.adapters.VariableColumnFactoryAdapter;
import org.eclipse.debug.internal.ui.elements.adapters.VariableColumnPresentation;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IColumnPresentation;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.key_project.sed.core.util.ISEDConstants;

/**
 * Extended {@link VariableColumnFactoryAdapter} to support {@link ISEDConstants#ID_CALL_STATE}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDBaseMethodReturnColumnPresentationFactory extends VariableColumnFactoryAdapter {
   /**
    * {@inheritDoc}
    */
   @Override
   public IColumnPresentation createColumnPresentation(IPresentationContext context, Object element) {
      if (ISEDConstants.ID_CALL_STATE.equals(context.getId())) {
         return new VariableColumnPresentation();
      }
      else {
         return super.createColumnPresentation(context, element);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getColumnPresentationId(IPresentationContext context, Object element) {
      if (ISEDConstants.ID_CALL_STATE.equals(context.getId())) {
         return VariableColumnPresentation.DEFAULT_VARIABLE_COLUMN_PRESENTATION;
      }
      else {
         return super.getColumnPresentationId(context, element);
      }
   }
}
