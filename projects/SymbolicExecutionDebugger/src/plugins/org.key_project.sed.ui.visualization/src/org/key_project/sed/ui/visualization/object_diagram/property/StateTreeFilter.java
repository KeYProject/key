package org.key_project.sed.ui.visualization.object_diagram.property;

import org.eclipse.jface.viewers.IFilter;

/**
 * {@link IFilter} implementation used to define if a {@link StatePropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class StateTreeFilter extends AbstractObjectDiagramTreeFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractObjectDiagramPropertySection<?> createPropertySection() {
      return new StatePropertySection();
   }
}
