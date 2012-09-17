package org.key_project.sed.ui.visualization.object_diagram.feature;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.AddConnectionContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.Anchor;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODFactory;
import org.key_project.sed.ui.visualization.model.od.ODModel;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODState;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.StringUtil;

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
    * The horizontal distance between {@link ODObject} in a diagram.
    */
   public static final int HORIZONTAL_OFFSET_BETWEEN_OBJECTS = 50;

   /**
    * The vertical distance between {@link ODObject} in a diagram.
    */
   public static final int VERTICAL_OFFSET_BETWEEN_OBJECTS = 50;
   
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
      SWTUtil.checkCanceled(monitor);
      // Get node
      ISEDDebugNode node = null;
      Object contextNode = context.getProperty(PROPERTY_NODE);
      if (contextNode instanceof ISEDDebugNode) {
         node = (ISEDDebugNode)contextNode;
      }
      // Generate model and diagram if possible
      try {
         if (node != null) {
            // Get model
            ODModel model = ObjectDiagramUtil.getModel(getDiagram());
            // Make sure that the model was not already generated
            if (model.getStates().isEmpty()) {
               // Create new model
               createState(model, node, monitor);
            }
         }
      }
      catch (OperationCanceledException e) {
         // Nothing to do.
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }
      finally {
         monitor.done();
      }
   }

   protected void createState(ODModel model, ISEDDebugNode node, IProgressMonitor monitor) throws DebugException {
      monitor.beginTask("Generating model and diagram.", IProgressMonitor.UNKNOWN);
      // Create sate
      ODState state = ODFactory.eINSTANCE.createODState();
      state.setName(StringUtil.toSingleLinedString(node.getName()));
      model.getStates().add(state);
      monitor.subTask(state.getName());
      // Fill state and instantiate objects
      if (node instanceof IStackFrame) {
         // Add values to state
         IStackFrame frame = (IStackFrame)node;
         IVariable[] variables = frame.getVariables();
         List<IVariable> objectVariables = fillValueContainer(variables, state, monitor);
         // Create state's PictogramElement
         PictogramElement statePE = addNodeToDiagram(state, 0, 0, 100, 100);
         // Instantiate child objects
         Map<String, PictogramElement> existingObjectsMap = new HashMap<String, PictogramElement>();
         analyzeVariables(objectVariables, 
                          state, 
                          statePE,
                          model, 
                          statePE.getGraphicsAlgorithm().getWidth() + HORIZONTAL_OFFSET_BETWEEN_OBJECTS,
                          statePE.getGraphicsAlgorithm().getY(),
                          existingObjectsMap,
                          monitor);
      }
      else {
         // Create state's PictogramElement
         addNodeToDiagram(state, 0, 0, 100, 100);
      }
      monitor.done();
   }
   
   protected List<IVariable> fillValueContainer(IVariable[] variables, 
                                                AbstractODValueContainer toFill,
                                                IProgressMonitor monitor) throws DebugException {
      List<IVariable> objectVariables = new LinkedList<IVariable>();
      for (IVariable variable : variables) {
         SWTUtil.checkCanceled(monitor);
         if (isMultiValued(variable)) {
            IVariable[] multiValuedVariables = variable.getValue().getVariables();
            for (IVariable multiValuedVariable : multiValuedVariables) {
               ODValue value = createValue(multiValuedVariable, toFill);
               if (value == null) {
                  objectVariables.add(multiValuedVariable);
               }
            }
         }
         else {
            ODValue value = createValue(variable, toFill);
            if (value == null) {
               objectVariables.add(variable);
            }
         }
      }
      return objectVariables;
   }
   
   protected ODValue createValue(IVariable variable, AbstractODValueContainer toFill) throws DebugException {
      if (!isObject(variable)) {
         ODValue value = ODFactory.eINSTANCE.createODValue();
         value.setName(StringUtil.toSingleLinedString(variable.getName()));
         value.setType(variable.getReferenceTypeName());
         value.setValue(StringUtil.toSingleLinedString(variable.getValue().getValueString()));
         toFill.getValues().add(value);
         return value;
      }
      else {
         return null;
      }
   }
   
   protected int analyzeVariables(List<IVariable> objectVariables, 
                                  AbstractODValueContainer toFill, 
                                  PictogramElement toFillPE,
                                  ODModel model, 
                                  int xForNewObjects,
                                  int yForNewObjects,
                                  Map<String, PictogramElement> existingObjectsMap,
                                  IProgressMonitor monitor) throws DebugException {
      int y = yForNewObjects;
      int maxWidth = 0;
      for (IVariable variable : objectVariables) {
         SWTUtil.checkCanceled(monitor);
         // Create object
         if (variable.getValue() != null) {
            // Get object name
            String objectName = variable.getValue().getValueString();
            PictogramElement objectPE = existingObjectsMap.get(objectName);
            if (objectPE != null) {
               // Create association
               ODAssociation association = ODFactory.eINSTANCE.createODAssociation();
               association.setName(StringUtil.toSingleLinedString(variable.getName()));
               association.setTarget((ODObject)getBusinessObjectForPictogramElement(objectPE));
               toFill.getAssociations().add(association);
               addConnectionToDiagram(association, toFillPE, objectPE);
            }
            else {
               ODObject object = ODFactory.eINSTANCE.createODObject();
               object.setName(StringUtil.toSingleLinedString(objectName));
               object.setType(variable.getReferenceTypeName());
               model.getObjects().add(object);
               monitor.subTask(object.getName());
               // Add values to object
               List<IVariable> childObjectVariables = fillValueContainer(variable.getValue().getVariables(), object, monitor);
               // Create object's PictogramElement
               objectPE = addNodeToDiagram(object, 
                                           xForNewObjects, 
                                           y, 
                                           100, 
                                           100);
               existingObjectsMap.put(objectName, objectPE);
               y += objectPE.getGraphicsAlgorithm().getHeight() + VERTICAL_OFFSET_BETWEEN_OBJECTS;
               if (objectPE.getGraphicsAlgorithm().getWidth() > maxWidth) {
                  maxWidth = objectPE.getGraphicsAlgorithm().getWidth();
               }
               // Create association
               ODAssociation association = ODFactory.eINSTANCE.createODAssociation();
               association.setName(StringUtil.toSingleLinedString(variable.getName()));
               association.setTarget(object);
               toFill.getAssociations().add(association);
               addConnectionToDiagram(association, toFillPE, objectPE);
               // Instantiate child objects
               int maxYChildren = analyzeVariables(childObjectVariables, 
                                                   object, 
                                                   objectPE,
                                                   model, 
                                                   xForNewObjects + maxWidth + HORIZONTAL_OFFSET_BETWEEN_OBJECTS, 
                                                   objectPE.getGraphicsAlgorithm().getY(),
                                                   existingObjectsMap,
                                                   monitor);
               if (maxYChildren > y) {
                  y = maxYChildren;
               }
            }            
         }
         monitor.worked(1);
      }
      return y;
   }
   
   /**
    * Checks if the given {@link IVariable} is multi valued.
    * @param variable The {@link IVariable} to check.
    * @return {@code true} is multi valued, {@code false} is single valued.
    * @throws DebugException Occurred Exception.
    */
   protected boolean isMultiValued(IVariable variable) throws DebugException {
      return variable.getValue() instanceof ISEDValue &&
             ((ISEDValue)variable.getValue()).isMultiValued();
   }
   
   /**
    * Checks if the given {@link IVariable} contains an object as value.
    * @param variable The {@link IVariable} to check.
    * @return {@code true} contains object as value, {@code false} contains object attribute as value.
    * @throws DebugException Occurred Exception.
    */
   protected boolean isObject(IVariable variable) throws DebugException {
      return variable.getValue() instanceof ISEDValue &&
             ((ISEDValue)variable.getValue()).isObject();
   }
   
   /**
    * Adds the given business object as new node to the diagram ({@link #getDiagram()}).
    * @param bo The business object to add.
    * @param x The x coordinate.
    * @param y The y coordinate.
    * @param width The width of the graphical representation.
    * @param height The height of the graphical representation.
    * @return The created {@link PictogramElement}.
    */
   protected PictogramElement addNodeToDiagram(Object bo, int x, int y, int width, int height) {
      AddContext context = new AddContext(new AreaContext(), bo);
      context.setTargetContainer(getDiagram());
      context.setLocation(x, y);
      context.setSize(width, height);
      context.putProperty(AbstractODValueContainerAddFeature.PROPERTY_UPDATE_SIZE, Boolean.TRUE);
      return getFeatureProvider().addIfPossible(context);
   }
   
   /**
    * Adds the given business object as new connection to the diagram ({@link #getDiagram()}).
    * @param bo The business object to add.
    * @param source The source {@link PictogramElement} which must be an instance of {@link AnchorContainer}.
    * @param target The target {@link PictogramElement} which must be an instance of {@link AnchorContainer}.
    * @return The created {@link PictogramElement}.
    */
   protected PictogramElement addConnectionToDiagram(Object bo, PictogramElement source, PictogramElement target) {
      Assert.isTrue(source instanceof AnchorContainer);
      Assert.isTrue(target instanceof AnchorContainer);
      Anchor sourceAnchor = CollectionUtil.getFirst(((AnchorContainer)source).getAnchors());
      Anchor targetAnchor = CollectionUtil.getFirst(((AnchorContainer)target).getAnchors());
      AddConnectionContext context = new AddConnectionContext(sourceAnchor, targetAnchor);
      context.setNewObject(bo);
      return getFeatureProvider().addIfPossible(context);
   }
}