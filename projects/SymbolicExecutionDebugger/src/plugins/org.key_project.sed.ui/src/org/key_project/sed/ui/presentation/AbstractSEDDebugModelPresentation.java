package org.key_project.sed.ui.presentation;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.debug.ui.IValueDetailListener;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDImages;
import org.key_project.util.java.StringUtil;

/**
 * Provides a basic implementation of {@link IDebugModelPresentation} 
 * for a Symbolic Execution Debugger (SED).
 * @author Martin Hentschel
 */
public abstract class AbstractSEDDebugModelPresentation extends LabelProvider implements IDebugModelPresentation {
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
      try {
         if (element instanceof ISEDDebugNode) {
            String name = ((ISEDDebugNode)element).getName();
            return StringUtil.toSingleLinedString(name);
         }
         else {
            return null; // Text is computed somewhere else in the Eclipse Debug API.
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return null; // Text is computed somewhere else in the Eclipse Debug API.
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage(Object element) {
      if (element instanceof ISEDDebugNode) {
         return SEDImages.getNodeImage((ISEDDebugNode)element);
      }
      else {
         return super.getImage(element);
      }
   }
}
