package org.key_project.sed.key.ui.property;

import org.eclipse.jface.viewers.IFilter;

/**
 * {@link IFilter} implementation used to define if a {@link MainKeYDebugTargetPropertySection}
 * or a {@link PerformanceKeYDebugTargetPropertySection} is available or not.
 * @author Martin Hentschel
 */
public class KeYDebugTargetTreeFilter implements IFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Object toTest) {
      return AbstractKeYDebugTargetPropertySection.getDebugTarget(toTest) != null;
   }
}
