package org.key_project.sed.ui.visualization.execution_tree.property;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.platform.AbstractPropertySectionFilter;
import org.eclipse.jface.viewers.IFilter;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * {@link IFilter} implementation used to define if a {@link SEDDebugNodePropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class SEDDebugNodeTreeFilter extends AbstractPropertySectionFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean accept(PictogramElement pe) {
      IWorkbenchPart part = WorkbenchUtil.getActivePart();
      boolean accept = false;
      if (part != null) {
         SEDDebugNodePropertySection section = new SEDDebugNodePropertySection();
         section.setInput(WorkbenchUtil.getActivePart(), null);
         IDiagramTypeProvider diagramProvider = section.getDiagramTypeProvider();
         if (diagramProvider != null) {
            IFeatureProvider featureProvider = diagramProvider.getFeatureProvider();
            if (featureProvider != null) {
               accept = featureProvider.getBusinessObjectForPictogramElement(pe) instanceof ISEDDebugNode;
            }
         }
      }
      return accept;
   }
}
