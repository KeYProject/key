package org.key_project.sed.ui.visualization.object_diagram.property;

import org.eclipse.jface.viewers.IFilter;

/**
 * {@link IFilter} implementation used to define if a {@link AssociationPropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class AssociationTreeFilter extends AbstractObjectDiagramTreeFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractObjectDiagramPropertySection<?> createPropertySection() {
      return new AssociationPropertySection();
   }
}
