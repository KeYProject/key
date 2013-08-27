package org.key_project.sed.key.ui.presentation;

import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.debug.ui.IValueDetailListener;
import org.eclipse.jdt.internal.debug.ui.JDIModelPresentation;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IEditorInput;
import org.key_project.sed.key.core.breakpoints.KeYWatchpoint;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDImages;

/**
 * This class defines the way a KeY Watchpoint is displayed in the Eclipse IDE.
 * 
 * @author Marco Drebing
 */
@SuppressWarnings("restriction")
public class KeYWatchpointModelPresentation extends LabelProvider implements IDebugModelPresentation {
   /**
    * Helper {@link IDebugModelPresentation} from Java Debug API.
    */
   private JDIModelPresentation helper = new JDIModelPresentation();
   @Override
   public void dispose() {
      super.dispose();
      helper.dispose();
   }
   
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

   @Override
   public String getEditorId(IEditorInput input, Object element) {
      return helper.getEditorId(input, element);
   }

   @Override
   public void setAttribute(String attribute, Object value) {
   }

   @Override
   public Image getImage(Object element) {
      if (element instanceof KeYWatchpoint) {
         return SEDImages.getImage(SEDImages.KEY_WATCHPOINT);
      }
      else {
         return super.getImage(element); // Image is computed somewhere else in the Eclipse Debug API.
      }
   }

   @Override
   public String getText(Object element) {
      try {
         if(element instanceof KeYWatchpoint){
            KeYWatchpoint watchpoint = (KeYWatchpoint)element;
            String result = watchpoint.getTypeName()+" ["+watchpoint.getCondition()+"] ";
            return result;
         }else{
            return null; // Text is computed somewhere else in the Eclipse Debug API.
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         return null; // Text is computed somewhere else in the Eclipse Debug API.
      }
   }

   @Override
   public void computeDetail(IValue value, IValueDetailListener listener) {
   }

}
