package org.key_project.sed.key.ui.presentation;

import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.debug.ui.IValueDetailListener;
import org.eclipse.jdt.internal.debug.ui.JDIModelPresentation;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.ui.IEditorInput;

/**
 * {@link IDebugModelPresentation} for the Symbolic Execution Debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYDebugModelPresentation extends LabelProvider implements IDebugModelPresentation {
   /**
    * Helper {@link IDebugModelPresentation} from Java Debug API.
    */
   private JDIModelPresentation helper = new JDIModelPresentation();
   
   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Copied from {@link JDIModelPresentation#getEditorInput(Object)}.
    * </p>
    */
   @Override
   public IEditorInput getEditorInput(Object element) {
      return helper.getEditorInput(element);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getEditorId(IEditorInput input, Object element) {
      return helper.getEditorId(input, element);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setAttribute(String attribute, Object value) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void computeDetail(IValue value, IValueDetailListener listener) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element) {
      return null; // Text is computed somewhere else in the Eclipse Debug API.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      super.dispose();
      helper.dispose();
   }
}
