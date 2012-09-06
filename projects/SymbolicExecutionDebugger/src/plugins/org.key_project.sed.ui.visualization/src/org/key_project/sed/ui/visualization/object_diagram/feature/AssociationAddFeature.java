package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IAddConnectionContext;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.impl.AbstractAddFeature;
import org.eclipse.graphiti.mm.GraphicsAlgorithmContainer;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ConnectionDecorator;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramStyleUtil;

/**
 * Implementation of {@link IAddFeature} for {@link ODAssociation}s.
 * @author Martin Hentschel
 */
public class AssociationAddFeature extends AbstractAddFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public AssociationAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canAdd(IAddContext context) {
      // return true if given business object is an EReference
      // note, that the context must be an instance of IAddConnectionContext
      if (context instanceof IAddConnectionContext && context.getNewObject() instanceof ODAssociation) {
         return true;
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PictogramElement add(IAddContext context) {
      IAddConnectionContext addConContext = (IAddConnectionContext) context;
      ODAssociation addedAssociation = (ODAssociation)context.getNewObject();
      IPeCreateService peCreateService = Graphiti.getPeCreateService();

      // CONNECTION WITH POLYLINE
      Connection connection = peCreateService.createFreeFormConnection(getDiagram());
      connection.setStart(addConContext.getSourceAnchor());
      connection.setEnd(addConContext.getTargetAnchor());

      IGaService gaService = Graphiti.getGaService();
      Polyline polyline = gaService.createPolyline(connection);
      polyline.setStyle(ObjectDiagramStyleUtil.getStyleForAssociation(getDiagram()));

      // create link and wire it
      link(connection, addedAssociation);

      // add dynamic text decorator for the association name
      ConnectionDecorator textDecorator = peCreateService.createConnectionDecorator(connection, true, 0.5, true);
      Text text = gaService.createDefaultText(getDiagram(), textDecorator);
      text.setStyle(ObjectDiagramStyleUtil.getStyleForAssociationText(getDiagram()));
      gaService.setLocation(text, 10, 0);
      // set reference name in the text decorator
      text.setValue(addedAssociation.getName());
      link(text.getPictogramElement(), addedAssociation);

      // add static graphical decorator (composition and navigable)
      ConnectionDecorator cd = peCreateService.createConnectionDecorator(connection, false, 1.0, true);
      createArrow(cd);
      return connection;
   }
   
   /**
    * Creates an arrow used in {@link ConnectionDecorator}s.
    * @param gaService The {@link IGaService} to use.
    * @param gaContainer The {@link GraphicsAlgorithmContainer} to use.
    * @return The created arrow {@link Polyline}.
    */
   protected Polyline createArrow(GraphicsAlgorithmContainer gaContainer) {
      IGaService gaService = Graphiti.getGaService();
      Polyline polyline = gaService.createPolyline(gaContainer, new int[] {-10, 5, 0, 0, -10, -5});
      polyline.setStyle(ObjectDiagramStyleUtil.getStyleForAssociation(getDiagram()));
      return polyline;
   }
}