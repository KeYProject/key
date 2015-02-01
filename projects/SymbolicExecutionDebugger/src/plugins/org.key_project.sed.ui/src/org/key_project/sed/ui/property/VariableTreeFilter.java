package org.key_project.sed.ui.property;

import org.eclipse.debug.core.model.IVariable;
import org.eclipse.jface.viewers.IFilter;

/**
 * An {@link IFilter} which selects {@link IVariable}s.
 * @author Martin Hentschel
 */
public class VariableTreeFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      return toTest instanceof IVariable;
   }
}
