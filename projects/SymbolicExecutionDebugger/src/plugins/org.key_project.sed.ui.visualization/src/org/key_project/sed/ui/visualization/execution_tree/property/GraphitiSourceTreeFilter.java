package org.key_project.sed.ui.visualization.execution_tree.property;

import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.platform.AbstractPropertySectionFilter;
import org.eclipse.jface.viewers.IFilter;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * {@link IFilter} implementation used to define if a {@link GraphitiSourcePropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class GraphitiSourceTreeFilter extends AbstractPropertySectionFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean accept(PictogramElement pe) {
      IWorkbenchPart part = WorkbenchUtil.getActivePart();
      if (part != null) {
         GraphitiSourcePropertySection section = new GraphitiSourcePropertySection();
         section.setInput(WorkbenchUtil.getActivePart(), null);
         return section.getStackFrame(pe) != null;
      }
      else {
         return false;
      }
   }
}
