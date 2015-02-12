package org.key_project.sed.ui.property;

import org.eclipse.jface.viewers.IFilter;
import org.key_project.sed.core.model.ISEDVariable;

/**
 * An {@link IFilter} which selects {@link ISEDVariable}s.
 * @author Martin Hentschel
 */
public class SEDVariableTreeFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      return toTest instanceof ISEDVariable;
   }
}
