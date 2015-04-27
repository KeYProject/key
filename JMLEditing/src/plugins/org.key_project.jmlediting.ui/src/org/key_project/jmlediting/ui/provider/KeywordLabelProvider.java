package org.key_project.jmlediting.ui.provider;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeyword;
import org.key_project.util.java.CollectionUtil;

/**
 * An {@link ITableLabelProvider} for {@link IUserDefinedKeyword}s.
 * @author Martin Hentschel
 */
public class KeywordLabelProvider extends LabelProvider implements ITableLabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getColumnText(Object element, int columnIndex) {
      if (element instanceof IKeyword) {
         switch (columnIndex) {
            case 0 : return CollectionUtil.toString(((IKeyword) element).getKeywords());
            case 1 : return ((IKeyword) element).getDescription();
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
