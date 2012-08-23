package org.key_project.sed.ui.visualization.execution_tree.property;

import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.platform.AbstractPropertySectionFilter;
import org.eclipse.jface.viewers.IFilter;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.sed.ui.property.AbstractSEDDebugNodeTabComposite;
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
         AbstractGraphitiDebugNodePropertySection section = new AbstractGraphitiDebugNodePropertySection() {
            @Override
            protected AbstractSEDDebugNodeTabComposite createContentComposite(Composite parent, int style) {
               return null; // Is never used.
            }
         };
         section.setInput(WorkbenchUtil.getActivePart(), null);
         return accept(pe, section);
      }
      else {
         return false;
      }
   }
   
   /**
    * Checks if the given {@link PictogramElement} should be accept in the given {@link AbstractGraphitiDebugNodePropertySection}.
    * @param pe The {@link PictogramElement} to check.
    * @param section The {@link AbstractGraphitiDebugNodePropertySection} to check.
    * @return {@code true} accept, {@code false} do not accept.
    */
   protected boolean accept(PictogramElement pe, AbstractGraphitiDebugNodePropertySection section) {
      return section.getDebugNode(pe) != null;
   }
}
