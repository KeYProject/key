package org.key_project.sed.ui.visualization.execution_tree.property;

import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.jface.viewers.IFilter;
import org.key_project.sed.ui.visualization.execution_tree.editor.ExecutionTreeDiagramEditor;

/**
 * {@link IFilter} implementation used to define if a {@link GraphitiCallStackPropertySection}
 * is available or not.
 * @author Martin Hentschel
 */
public class GraphitiReadonlyDebugNodeTreeFilter extends GraphitiDebugNodeTreeFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean accept(PictogramElement pe, AbstractGraphitiDebugNodePropertySection section) {
      if (super.accept(pe, section)) {
         if (section.getDiagramEditor() instanceof ExecutionTreeDiagramEditor) {
            return ((ExecutionTreeDiagramEditor)section.getDiagramEditor()).isReadOnly();
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }
}
