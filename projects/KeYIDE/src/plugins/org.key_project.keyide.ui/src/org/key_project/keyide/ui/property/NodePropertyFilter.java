package org.key_project.keyide.ui.property;

import org.eclipse.jface.viewers.IFilter;

/**
 * The used {@link IFilter} to define if the {@link NodePropertySection} is shown or not.
 * @author Martin Hentschel
 */
public class NodePropertyFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      return true;
   }
}
