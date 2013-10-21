package org.key_project.keyide.ui.property;

import org.eclipse.jface.viewers.IFilter;

/**
 * The used {@link IFilter} to define if the {@link TacletPropertySection} is shown or not.
 * @author Martin Hentschel
 */
public class TacletPropertyFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      return true;
   }
}
