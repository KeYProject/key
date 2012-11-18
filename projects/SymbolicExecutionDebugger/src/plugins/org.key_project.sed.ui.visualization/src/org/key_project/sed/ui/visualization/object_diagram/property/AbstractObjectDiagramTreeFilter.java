package org.key_project.sed.ui.visualization.object_diagram.property;

import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.platform.AbstractPropertySectionFilter;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Provides a basic implementation to decide for a given business object
 * if an {@link AbstractObjectDiagramPropertySection} is supported or not.
 * @author Martin Hentschel
 */
public abstract class AbstractObjectDiagramTreeFilter extends AbstractPropertySectionFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean accept(PictogramElement pe) {
      IWorkbenchPart part = WorkbenchUtil.getActivePart();
      if (part != null) {
         AbstractObjectDiagramPropertySection<?> section = createPropertySection();
         section.setInput(WorkbenchUtil.getActivePart(), null);
         return section.getBusinessObject(pe) != null;
      }
      else {
         return false;
      }
   }

   /**
    * Creates an {@link AbstractObjectDiagramPropertySection} which is used to check if the tab page is supported or not.
    * @return The instantiated {@link AbstractObjectDiagramPropertySection}.
    */
   protected abstract AbstractObjectDiagramPropertySection<?> createPropertySection();
}
