package org.key_project.sed.ui.provider;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.slicing.ISEDSlicer;
import org.key_project.sed.ui.util.SEDImages;

/**
 * {@link LabelProvider} used for {@link ISEDSlicer}.
 * @author Martin Hentschel
 */
public class SEDSlicerLabelProvider extends LabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element) {
      if (element instanceof ISEDSlicer) {
         return ((ISEDSlicer) element).getName();
      }
      else {
         return super.getText(element);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage(Object element) {
      if (element instanceof ISEDSlicer) {
         return SEDImages.getImage(SEDImages.SLICE);
      }
      else {
         return super.getImage(element);
      }
   }
}
