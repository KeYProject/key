package org.key_project.sed.ui.presentation;

import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.debug.ui.IValueDetailListener;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.ui.util.SEDImages;

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
      return null; // Text is computed somewhere else in the Eclipse Debug API.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage(Object element) {
      if (element instanceof ISEDMethodCall) {
         return SEDImages.getImage(SEDImages.METHOD_CALL);
      }
      else if (element instanceof ISEDMethodReturn) {
         return SEDImages.getImage(SEDImages.METHOD_RETURN);
      }
      else if (element instanceof ISEDExceptionalTermination) {
         return SEDImages.getImage(SEDImages.EXCEPTIONAL_TERMINATION);
      }
      else if (element instanceof ISEDTermination) {
         return SEDImages.getImage(SEDImages.TERMINATION);
      }
      else if (element instanceof ISEDBranchCondition) {
         return SEDImages.getImage(SEDImages.BRANCH_CONDITION);
      }
      else if (element instanceof ISEDBranchNode) {
         return SEDImages.getImage(SEDImages.BRANCH_NODE);
      }
      else {
         return super.getImage(element);
      }
   }
}
