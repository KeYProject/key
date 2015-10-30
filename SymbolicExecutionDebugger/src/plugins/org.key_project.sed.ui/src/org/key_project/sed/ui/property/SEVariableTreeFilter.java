package org.key_project.sed.ui.property;

import org.eclipse.jface.viewers.IFilter;
import org.key_project.sed.core.model.ISEVariable;

/**
 * An {@link IFilter} which selects {@link ISEVariable}s.
 * @author Martin Hentschel
 */
public class SEVariableTreeFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      return toTest instanceof ISEVariable;
   }
}
