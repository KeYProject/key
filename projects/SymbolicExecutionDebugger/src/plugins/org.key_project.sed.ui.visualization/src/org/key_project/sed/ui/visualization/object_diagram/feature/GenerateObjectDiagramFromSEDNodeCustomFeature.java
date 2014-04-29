/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.ui.visualization.object_diagram.feature;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.Diagram;
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

/**
 * An {@link ICustomFeature} that generates an object diagram based
 * on the state provided via an {@link ISEDDebugNode}.
 * The {@link ISEDDebugNode} is specified via property {@link #PROPERTY_NODE} 
 * of the given {@link ICustomContext}.
 * @author Martin Hentschel
 */
public class GenerateObjectDiagramFromSEDNodeCustomFeature extends AbstractGenerateObjectDiagramCustomFeature {
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
   public void execute(ICustomContext context) {
      // Get monitor
      IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
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
               PictogramElement statePE = createState(model, node, monitor);
               // Improve diagram layout
               improveLayout(model, monitor);
               // Select statePE
               GraphitiUtil.select(getFeatureProvider(), statePE);
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

   /**
    * Creates the {@link ODState}.
    * @param model The {@link ODModel} to fill.
    * @param node The {@link ISEDDebugNode} to visualize its state. 
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The {@link PictogramElement} of the created state.
    * @throws DebugException Occurred Exception.
    */
   protected PictogramElement createState(ODModel model, ISEDDebugNode node, IProgressMonitor monitor) throws DebugException {
      monitor.beginTask("Generating model and diagram.", IProgressMonitor.UNKNOWN);
      // Create state
      ODState state = ODFactory.eINSTANCE.createODState();
      state.setName(node.getName());
      model.getStates().add(state);
      monitor.subTask(state.getName());
      // Fill state and instantiate objects
      PictogramElement statePE;
      if (node instanceof IStackFrame) {
         // Add values to state
         IStackFrame frame = (IStackFrame)node;
         IVariable[] variables = frame.getVariables();
         List<IVariable> objectVariables = fillValueContainer(variables, state, monitor);
         // Create state's PictogramElement
         statePE = addNodeToDiagram(state, 0, 0);
         // Instantiate child objects
         Map<String, PictogramElement> existingObjectsMap = new HashMap<String, PictogramElement>();
         analyzeVariables(objectVariables, 
                          state, 
                          statePE,
                          model, 
                          statePE.getGraphicsAlgorithm().getY(),
                          existingObjectsMap,
                          monitor);
      }
      else {
         // Create state's PictogramElement
         statePE = addNodeToDiagram(state, 0, 0);
      }
      monitor.done();
      return statePE;
   }
   
   /**
    * Fills the given {@link AbstractODValueContainer} with the content
    * of {@link IVariable} which represents no object. {@link IVariable} which
    * represents objects are collected and returned as result.
    * @param variables The {@link IVariable}s to analyze.
    * @param toFill The {@link AbstractODValueContainer} to fill.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return Skipped {@link IVariable}s which represents objects.
    * @throws DebugException Occurred Exception.
    */
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
   
   /**
    * Creates an {@link ODValue} with the content provided by the given {@link IVariable}.
    * @param variable The {@link IVariable} which provides the content.
    * @param toFill The parent {@link AbstractODValueContainer} to add new {@link ODValue} to.
    * @return The created {@link ODValue}.
    * @throws DebugException Occurred Exception.
    */
   protected ODValue createValue(IVariable variable, AbstractODValueContainer toFill) throws DebugException {
      if (!isObject(variable)) {
         ODValue value = ODFactory.eINSTANCE.createODValue();
         value.setName(variable.getName());
         value.setType(variable.getReferenceTypeName());
         value.setValue(variable.getValue().getValueString());
         toFill.getValues().add(value);
         return value;
      }
      else {
         return null;
      }
   }
   
   /**
    * Iterates recursive over the given {@link IVariable}s which represents
    * objects and adds them to the {@link Diagram}. This method visualizes
    * on this way the complete visible heap.
    * @param objectVariables The {@link IVariable} which represents objects to instantiate {@link ODObject}s for.
    * @param toFill The parent {@link AbstractODValueContainer} to fill with {@link ODAssociation}s.
    * @param toFillPE The graphical representation of the parent {@link AbstractODValueContainer}.
    * @param model The {@link ODModel} to fill.
    * @param yForNewObjects The y coordinate for new objects.
    * @param existingObjectsMap A map which contains already visualized {@link ODObject}s.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The y coordinate for new child objects.
    * @throws DebugException Occurred Exception.
    */
   protected int analyzeVariables(List<IVariable> objectVariables, 
                                  AbstractODValueContainer toFill, 
                                  PictogramElement toFillPE,
                                  ODModel model,
                                  int yForNewObjects,
                                  Map<String, PictogramElement> existingObjectsMap,
                                  IProgressMonitor monitor) throws DebugException {
      int y = yForNewObjects;
      for (IVariable variable : objectVariables) {
         SWTUtil.checkCanceled(monitor);
         // Create object
         if (variable.getValue() != null) {
            // Get object name
            String objectName = variable.getValue().getValueString();
            PictogramElement objectPE = existingObjectsMap.get(objectName);
            if (objectPE != null) {
               // Create association
               createAssociation(toFill, toFillPE, variable.getName(), (ODObject)getBusinessObjectForPictogramElement(objectPE), objectPE);
            }
            else {
               ODObject object = ODFactory.eINSTANCE.createODObject();
               object.setName(objectName);
               object.setType(variable.getReferenceTypeName());
               model.getObjects().add(object);
               monitor.subTask(object.getName());
               // Add values to object
               List<IVariable> childObjectVariables = fillValueContainer(variable.getValue().getVariables(), object, monitor);
               // Create object's PictogramElement
               objectPE = addNodeToDiagram(object, 
                                           toFillPE.getGraphicsAlgorithm().getX() + toFillPE.getGraphicsAlgorithm().getWidth() + HORIZONTAL_OFFSET_BETWEEN_OBJECTS, 
                                           y);
               existingObjectsMap.put(objectName, objectPE);
               y += objectPE.getGraphicsAlgorithm().getHeight() + VERTICAL_OFFSET_BETWEEN_OBJECTS;
               // Create association
               createAssociation(toFill, toFillPE, variable.getName(), object, objectPE);
               // Instantiate child objects
               int maxYChildren = analyzeVariables(childObjectVariables, 
                                                   object, 
                                                   objectPE,
                                                   model, 
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
    * Creates a new {@link ODAssociation} and adds it to the diagram.
    * @param toFill The {@link AbstractODValueContainer} to fill.
    * @param toFillPE The {@link PictogramElement} of the {@link AbstractODValueContainer}.
    * @param associationName The The name of the association.
    * @param object The target {@link ODObject}.
    * @param objectPE The {@link PictogramElement} of the target {@link ODObject}.
    */
   protected PictogramElement createAssociation(AbstractODValueContainer toFill, 
                                                PictogramElement toFillPE, 
                                                String associationName, 
                                                ODObject object,
                                                PictogramElement objectPE) {
      ODAssociation association = ODFactory.eINSTANCE.createODAssociation();
      association.setName(associationName);
      association.setTarget(object);
      toFill.getAssociations().add(association);
      PictogramElement associationPE = addConnectionToDiagram(association, toFillPE, objectPE);
      return associationPE;
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
}