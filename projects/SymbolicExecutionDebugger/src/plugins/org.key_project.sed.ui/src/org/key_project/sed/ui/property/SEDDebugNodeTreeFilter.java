package org.key_project.sed.ui.property;

import org.eclipse.jface.viewers.IFilter;

/**
 * {@link IFilter} implementation used to define if a {@link SEDDebugNodePropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class SEDDebugNodeTreeFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      return SEDDebugNodePropertySection.getDebugNode(toTest) != null;
   }
}
