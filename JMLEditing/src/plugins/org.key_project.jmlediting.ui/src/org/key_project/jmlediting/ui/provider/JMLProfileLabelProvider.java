package org.key_project.jmlediting.ui.provider;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;

/**
 * An {@link ITableLabelProvider} for {@link IJMLProfile}s.
 * @author Martin Hentschel
 */
public class JMLProfileLabelProvider extends LabelProvider implements ITableLabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getColumnText(Object element, int columnIndex) {
      if (element instanceof IJMLProfile) {
         switch (columnIndex) {
            case 0 : return ((IJMLProfile) element).getName();
            case 1 : return computeType((IJMLProfile) element);
            default : return null;
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Computes the profile type.
    * @param profile The given {@link IJMLProfile}.
    * @return The type of the given {@link IJMLProfile}.
    */
   protected String computeType(IJMLProfile profile) {
      if (profile instanceof IDerivedProfile) {
         return "derived from " + ((IDerivedProfile) profile).getParentProfile().getName();
      }
      else {
         return "standalone";
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
