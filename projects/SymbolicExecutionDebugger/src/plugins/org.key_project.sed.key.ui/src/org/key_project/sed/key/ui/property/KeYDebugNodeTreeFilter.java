package org.key_project.sed.key.ui.property;

import org.eclipse.jface.viewers.IFilter;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;

/**
 * {@link IFilter} implementation used to define if a {@link KeYDebugNodePropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class KeYDebugNodeTreeFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      return toTest instanceof IKeYSEDDebugNode<?>;
   }
}
