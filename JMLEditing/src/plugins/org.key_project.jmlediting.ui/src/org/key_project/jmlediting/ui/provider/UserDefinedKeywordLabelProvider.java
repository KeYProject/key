package org.key_project.jmlediting.ui.provider;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeyword;
import org.key_project.util.java.CollectionUtil;

/**
 * An {@link ITableLabelProvider} for {@link IUserDefinedKeyword}s.
 * @author Martin Hentschel
 */
public class UserDefinedKeywordLabelProvider extends LabelProvider implements ITableLabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getColumnText(Object element, int columnIndex) {
      if (element instanceof IUserDefinedKeyword) {
         switch (columnIndex) {
            case 0 : return CollectionUtil.toString(((IUserDefinedKeyword) element).getKeywords());
            case 1 : return ((IUserDefinedKeyword) element).getContentDescription().getDescription();
            case 2 : return ((IUserDefinedKeyword) element).getDescription();
            default : return null;
         }
      }
      else {
         return null;
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
