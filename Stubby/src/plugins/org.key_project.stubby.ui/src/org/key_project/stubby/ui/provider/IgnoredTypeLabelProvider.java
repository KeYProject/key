package org.key_project.stubby.ui.provider;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.stubby.core.util.StubGeneratorUtil.IgnoredType;

/**
 * An {@link ITableLabelProvider} for {@link IgnoredType}s.
 * @author Martin Hentschel
 */
public class IgnoredTypeLabelProvider extends LabelProvider implements ITableLabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getColumnText(Object element, int columnIndex) {
      if (element instanceof IgnoredType) {
         switch (columnIndex) {
            case 0 : return ((IgnoredType) element).getType().getName();
            case 1 : return ((IgnoredType) element).getReason();
            default : return super.getText(element);
         }
      }
      else {
         return super.getText(element);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getColumnImage(Object element, int columnIndex) {
      return null;
   }
}
