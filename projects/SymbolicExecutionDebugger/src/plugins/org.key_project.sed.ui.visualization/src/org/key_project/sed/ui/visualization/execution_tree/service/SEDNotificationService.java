package org.key_project.sed.ui.visualization.execution_tree.service;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IUpdateContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.notification.DefaultNotificationService;
import org.eclipse.graphiti.notification.INotificationService;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;

/**
 * Implementation of {@link INotificationService} for Symbolic Execution Tree digrams.
 * @author Martin Hentschel
 * @see ExecutionTreeDiagramTypeProvider
 */
public class SEDNotificationService extends DefaultNotificationService {
   /**
    * Constructor.
    * @param diagramTypeProvider The {@link IDiagramTypeProvider} in which this {@link INotificationService} is used.
    */
   public SEDNotificationService(IDiagramTypeProvider diagramTypeProvider) {
      super(diagramTypeProvider);
   }

   /**
    * <p>
    * Updates the defined {@link PictogramElement}s.
    * </p>
    * <p>
    * The code was copied from {@link DefaultNotificationService#updatePictogramElements(PictogramElement[])} and modified.
    * </p>
    * @param dirtyPes The {@link PictogramElement}s to update.
    * @param monitor The {@link IProgressMonitor} to set via property {@link ExecutionTreeUtil#CONTEXT_PROPERTY_MONITOR} in the used {@link IUpdateContext}.
    */
   public void updatePictogramElements(PictogramElement[] dirtyPes, IProgressMonitor monitor) {
      final IDiagramTypeProvider dtp = getDiagramTypeProvider();
      final IFeatureProvider fp = dtp.getFeatureProvider();
      for (PictogramElement pe : dirtyPes) {
         final UpdateContext updateContext = new UpdateContext(pe);
         updateContext.putProperty(ExecutionTreeUtil.CONTEXT_PROPERTY_MONITOR, monitor);
         // fp.updateIfPossible(updateContext);
         fp.updateIfPossibleAndNeeded(updateContext);
      }
   }
}
