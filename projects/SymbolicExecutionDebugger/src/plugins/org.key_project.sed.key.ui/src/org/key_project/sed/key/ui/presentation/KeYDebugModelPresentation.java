package org.key_project.sed.key.ui.presentation;

import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.jdt.internal.debug.ui.JDIModelPresentation;
import org.eclipse.ui.IEditorInput;
import org.key_project.sed.ui.presentation.AbstractSEDDebugModelPresentation;

/**
 * {@link IDebugModelPresentation} for the Symbolic Execution Debugger (SED)
 * based on KeY.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYDebugModelPresentation extends AbstractSEDDebugModelPresentation implements IDebugModelPresentation {
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
   public void dispose() {
      super.dispose();
      helper.dispose();
   }
}
