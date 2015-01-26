package org.key_project.sed.key.ui.counterExample;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.CustomContext;
import org.key_project.key4eclipse.common.ui.counterExample.AbstractModelContextMenuAction;
import org.key_project.key4eclipse.common.ui.counterExample.EclipseCounterExampleGenerator;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.sed.key.ui.visualization.object_diagram.feature.GenerateObjectDiagramFromModelCustomFeature;
import org.key_project.sed.ui.visualization.object_diagram.editor.ReadonlyObjectDiagramEditor;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.smt.model.Model;

/**
 * Visualizes the current {@link Model} as symbolic object diagram.
 * @author Martin Hentschel
 */
public class VisualizeModelContextMenuAction extends AbstractModelContextMenuAction {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getText() {
      return "Visualize Model";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void run() {
      try {
         // Open editor
         String problemName = EclipseCounterExampleGenerator.computeProblemName(getProblem());
         ReadonlyObjectDiagramEditor readonlyEditor = ReadonlyObjectDiagramEditor.openEditor(WorkbenchUtil.getActivePage(), problemName, EclipseCounterExampleGenerator.computeProblemId(getProblem()));
         // Generate object diagram if not already available
         if (!ObjectDiagramUtil.hasModel(readonlyEditor.getDiagramTypeProvider().getDiagram())) {
            IDiagramTypeProvider typeProvider = readonlyEditor.getDiagramTypeProvider();
            IFeatureProvider featureProvider = typeProvider.getFeatureProvider();
            IFeature feature = new GenerateObjectDiagramFromModelCustomFeature(featureProvider);
            ICustomContext context = new CustomContext();
            context.putProperty(GenerateObjectDiagramFromModelCustomFeature.PROPERTY_MODEL, getModel());
            context.putProperty(GenerateObjectDiagramFromModelCustomFeature.PROPERTY_MODEL_NAME, problemName);
            readonlyEditor.executeFeatureInJob("Generating Object Diagram for \"" + problemName + "\"", feature, context);
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
      }
   }
}
