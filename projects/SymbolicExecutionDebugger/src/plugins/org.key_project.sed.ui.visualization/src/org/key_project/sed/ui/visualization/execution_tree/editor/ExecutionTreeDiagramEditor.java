package org.key_project.sed.ui.visualization.execution_tree.editor;

import java.io.OutputStream;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeFeatureProvider;
import org.key_project.sed.ui.visualization.execution_tree.service.SEDIndependenceSolver;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;

/**
 * {@link DiagramEditor} for Symbolic Execution Tree Diagrams.
 * @author Martin Hentschel
 */
// TODO: Reload diagram when the domain model file has changed.
public class ExecutionTreeDiagramEditor extends DiagramEditor {
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   public void doSave(IProgressMonitor monitor) {
      try {
         // Save diagram file
         super.doSave(monitor);
         // Save domain file
         IDiagramTypeProvider diagramTypeProvider = getDiagramTypeProvider();
         if (diagramTypeProvider != null) {
            IFeatureProvider featureProvider = diagramTypeProvider.getFeatureProvider();
            if (featureProvider instanceof ExecutionTreeFeatureProvider) {
               // Get solver which provides the domain objects
               SEDIndependenceSolver solver = ((ExecutionTreeFeatureProvider)featureProvider).getSEDIndependenceSolver();
               // Open output stream to domain file
               OutputStream out = ExecutionTreeUtil.writeDomainFile(diagramTypeProvider.getDiagram());
               // Save domain file
               SEDXMLWriter writer = new SEDXMLWriter();
               writer.write(solver.getDebugTargets(), SEDXMLWriter.DEFAULT_ENCODING, out);
            }
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         throw new RuntimeException(e);
      }
   }
}
