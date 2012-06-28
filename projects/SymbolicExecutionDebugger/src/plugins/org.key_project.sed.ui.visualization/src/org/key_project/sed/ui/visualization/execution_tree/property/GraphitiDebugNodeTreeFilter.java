package org.key_project.sed.ui.visualization.execution_tree.property;

import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.platform.AbstractPropertySectionFilter;
import org.eclipse.jface.viewers.IFilter;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * {@link IFilter} implementation used to define if a {@link GraphitiDebugNodePropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class GraphitiDebugNodeTreeFilter extends AbstractPropertySectionFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean accept(PictogramElement pe) {
      IWorkbenchPart part = WorkbenchUtil.getActivePart();
      if (part != null) {
         GraphitiDebugNodePropertySection section = new GraphitiDebugNodePropertySection();
         section.setInput(WorkbenchUtil.getActivePart(), null);
         return section.getDebugNode(pe) != null;
      }
      else {
         return false;
      }
   }
}
