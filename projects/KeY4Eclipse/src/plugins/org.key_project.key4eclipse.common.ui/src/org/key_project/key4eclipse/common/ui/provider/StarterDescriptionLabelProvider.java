package org.key_project.key4eclipse.common.ui.provider;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.key_project.key4eclipse.common.ui.util.StarterDescription;

/**
 * An {@link ILabelProvider} for {@link StarterDescription}s.
 * @author Martin Hentschel
 */
public class StarterDescriptionLabelProvider extends LabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element) {
      if (element instanceof StarterDescription<?>) {
         return ((StarterDescription<?>)element).getName();
      }
      else {
         return super.getText(element);
      }
   }
}
