package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.model.od.ODFactory;
import org.key_project.sed.ui.visualization.model.od.ODModel;
import org.key_project.sed.ui.visualization.model.od.ODState;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;

/**
 * An {@link ICustomFeature} that generates an object diagram based
 * on the state provided via an {@link ISEDDebugNode}.
 * The {@link ISEDDebugNode} is specified via property {@link #PROPERTY_NODE} 
 * of the given {@link ICustomContext}.
 * @author Martin Hentschel
 */
public class GenerateObjectDiagramFromSEDNodeCustomFeature extends AbstractCustomFeature {
   /**
    * Property for an {@link ISEDDebugNode} instance which provides
    * the state to visualize as object diagram.
    */
   public static final String PROPERTY_NODE = "debugNode";

   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public GenerateObjectDiagramFromSEDNodeCustomFeature(IFeatureProvider fp) {
      super(fp);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canExecute(ICustomContext context) {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void execute(ICustomContext context) {
      // Get monitor
      IProgressMonitor monitor;
      Object contextMonitor = context.getProperty(GraphitiUtil.CONTEXT_PROPERTY_MONITOR);
      if (contextMonitor instanceof IProgressMonitor) {
         monitor = (IProgressMonitor)contextMonitor;
      }
      else {
         monitor = new NullProgressMonitor();
      }
      // Get node
      ISEDDebugNode node = null;
      Object contextNode = context.getProperty(PROPERTY_NODE);
      if (contextNode instanceof ISEDDebugNode) {
         node = (ISEDDebugNode)contextNode;
      }
      // Generate model and diagram if possible
      try {
         if (node != null) {
            // Generate model
            ODModel model = ObjectDiagramUtil.getModel(getDiagram());
            // Make sure that the model was not already generated
            if (model.getStates().isEmpty()) {
               monitor.beginTask("Generating Object Diagram for \"" + node.getName() + "\"", 2);
               monitor.subTask("Generating model.");
               fillModel(model, node, new SubProgressMonitor(monitor, IProgressMonitor.UNKNOWN));
               monitor.worked(1);
               // Generate diagram
               monitor.subTask("Generating diagram from model.");
               fillDiagram(model, new SubProgressMonitor(monitor, IProgressMonitor.UNKNOWN));
               monitor.worked(1);
            }
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }
      finally {
         monitor.done();
      }
   }

   /**
    * Fills the given {@link ODModel} with the content provided by the {@link ISEDDebugNode}.
    * @param model The {@link ODModel} to fill.
    * @param node The {@link ISEDDebugNode} which provides the state to visualize.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected void fillModel(ODModel model, ISEDDebugNode node, IProgressMonitor monitor) throws DebugException {
      ODState state = ODFactory.eINSTANCE.createODState();
      state.setName(node.getName());
      model.getStates().add(state);
   }

   /**
    * Fills {@link #getDiagram()} with the content provided by the {@link ODModel}.
    * @param model The {@link ODModel} which provides the content to show.
    * @param monitor The {@link IProgressMonitor} to use.
    */
   protected void fillDiagram(ODModel model, IProgressMonitor monitor) {
      for (ODState state : model.getStates()) {
         AddContext context = new AddContext(new AreaContext(), state);
         context.setTargetContainer(getDiagram());
         context.setLocation(10, 10);
         context.setSize(100, 100);
         addGraphicalRepresentation(context, state);
      }
   }
}