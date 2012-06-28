package org.key_project.sed.ui.property;

import org.eclipse.jface.viewers.IFilter;

/**
 * {@link IFilter} implementation used to define if a {@link SourcePropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class SourceTreeFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      return SourcePropertySection.getStackFrame(toTest) != null;
   }
}
