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

package org.key_project.sed.key.ui.visualization.object_diagram.feature;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODFactory;
import org.key_project.sed.ui.visualization.model.od.ODModel;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODState;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.feature.AbstractGenerateObjectDiagramCustomFeature;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.gui.smt.CETree;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.util.Pair;

/**
 * An {@link ICustomFeature} that generates an object diagram based
 * on the state provided via a {@link Model}.
 * The {@link ISENode} is specified via property {@link #PROPERTY_MODEL} 
 * of the given {@link ICustomContext}.
 * @author Martin Hentschel
 */
public class GenerateObjectDiagramFromModelCustomFeature extends AbstractGenerateObjectDiagramCustomFeature {
   /**
    * Property for an {@link ISENode} instance which provides
    * the state to visualize as object diagram.
    */
   public static final String PROPERTY_MODEL = "model";
   
   /**
    * Property for an {@link ISENode} instance which provides
    * the state to visualize as object diagram.
    */
   public static final String PROPERTY_MODEL_NAME = "modelName";
   
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public GenerateObjectDiagramFromModelCustomFeature(IFeatureProvider fp) {
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
      // Get model
      Model model = null;
      Object contextModel = context.getProperty(PROPERTY_MODEL);
      if (contextModel instanceof Model) {
         model = (Model)contextModel;
      }
      String modelName = ObjectUtil.toString(context.getProperty(PROPERTY_MODEL_NAME));
      // Generate model and diagram if possible
      try {
         if (model != null) {
            // Get model
            ODModel diagramModel = ObjectDiagramUtil.getModel(getDiagram());
            // Make sure that the model was not already generated
            if (diagramModel.getStates().isEmpty()) {
               // Create new model
               PictogramElement statePE = createStateAndObjects(diagramModel, model, modelName, monitor);
               // Improve diagram layout
               improveLayout(diagramModel, monitor);
               // Select statePE
               GraphitiUtil.select(getFeatureProvider(), statePE);
            }
         }
      }
      catch (OperationCanceledException e) {
         // Nothing to do.
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
      finally {
         monitor.done();
      }
   }

   /**
    * Creates the {@link ODState} and all {@link ODObject}s including {@link ODValue}s and {@link ODAssociation}s.
    * @param diagramModel The {@link ODModel} to fill.
    * @param model The {@link Model} to analyze.
    * @param modelName The Name of the model.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The {@link PictogramElement} of the created {@link ODState}.
    */
   protected PictogramElement createStateAndObjects(ODModel diagramModel, 
                                                    Model model, 
                                                    String modelName, 
                                                    IProgressMonitor monitor) {
      // Create state;
      ODState diagramState = ODFactory.eINSTANCE.createODState();
      diagramState.setName(modelName);
      diagramModel.getStates().add(diagramState);
      // Create objects
      Map<Heap, Map<String, ODObject>> heapObjectMap = new HashMap<Heap, Map<String, ODObject>>();
      Map<AbstractODValueContainer, PictogramElement> containerPEMap = new HashMap<AbstractODValueContainer, PictogramElement>();
      Map<ObjectVal, ODObject> objectValMap = new HashMap<ObjectVal, ODObject>();
      for (Heap heap : model.getHeaps()) {
         Map<String, ODObject> objectMap = new HashMap<String, ODObject>();
         heapObjectMap.put(heap, objectMap);
         for (ObjectVal ov : heap.getObjects()) {
            String sortName = CETree.computeSortName(ov);
            ODObject diagramObject = ODFactory.eINSTANCE.createODObject();
            diagramObject.setName(ov.getName() + "@" + heap.getName());
            diagramObject.setType(sortName);
            diagramModel.getObjects().add(diagramObject);
            objectValMap.put(ov, diagramObject);
            String[] names = ov.getName().split("/");
            for (String name : names) {
               assert !objectMap.containsKey(name);
               objectMap.put(name, diagramObject);
            }
            monitor.worked(1);
         }
      }
      // Fill object with fields
      List<Pair<ODAssociation, AbstractODValueContainer>> associations = new LinkedList<Pair<ODAssociation, AbstractODValueContainer>>();
      for (Heap heap : model.getHeaps()) {
         Map<String, ODObject> objectMap = heapObjectMap.get(heap);
         for (ObjectVal ov : heap.getObjects()) {
            ODObject diagramObject = objectValMap.get(ov);
            String sortName = CETree.computeSortName(ov);
            List<Pair<String, String>> properties = CETree.computeObjectProperties(ov, sortName);
            createValuesAndAssociations(objectMap, properties, diagramObject, associations);
            List<Pair<String, String>> fields = CETree.computeFields(ov);
            createValuesAndAssociations(objectMap, fields, diagramObject, associations);
            List<Pair<String, String>> functions = CETree.computeFunctions(ov);
            createValuesAndAssociations(objectMap, functions, diagramObject, associations);
            PictogramElement objectPE = addNodeToDiagram(diagramObject, 0, 0);
            containerPEMap.put(diagramObject, objectPE);
            monitor.worked(1);
         }
      }
      // Fill state with fields
      List<Pair<String, String>> constants = CETree.computeConstantLabels(model);
      createStateValuesAndAssociations(heapObjectMap, constants, diagramState, associations);
      // Create association PEs
      PictogramElement statePE = addNodeToDiagram(diagramState, 0, 0);
      containerPEMap.put(diagramState, statePE);
      for (Pair<ODAssociation, AbstractODValueContainer> pair : associations) {
         addConnectionToDiagram(pair.first, containerPEMap.get(pair.second), containerPEMap.get(pair.first.getTarget()));
         monitor.worked(1);
      }
      return statePE;
   }
   
   /**
    * Creates for the given {@link Pair}s {@link ODValue} or {@link ODAssociation}s.
    * @param objectMap The {@link Map} which maps object name to {@link ODObject}s.
    * @param contentToAdd The {@link Pair}s to analyze.
    * @param containerToFill The {@link AbstractODValueContainer} to fill.
    * @param associations The {@link List} which contains all available {@link ODAssociation}s.
    */
   protected void createValuesAndAssociations(Map<String, ODObject> objectMap, 
                                              List<Pair<String, String>> contentToAdd, 
                                              AbstractODValueContainer containerToFill, 
                                              List<Pair<ODAssociation, AbstractODValueContainer>> associations) {
      for (Pair<String, String> constant : contentToAdd) {
         ODObject diagramObject = objectMap.get(constant.second);
         if (diagramObject != null) {
            ODAssociation diagramAssociation = ODFactory.eINSTANCE.createODAssociation();
            diagramAssociation.setName(constant.first);
            diagramAssociation.setTarget(diagramObject);
            containerToFill.getAssociations().add(diagramAssociation);
            associations.add(new Pair<ODAssociation, AbstractODValueContainer>(diagramAssociation, containerToFill));
         }
         else {
            ODValue diagramValue = ODFactory.eINSTANCE.createODValue();
            diagramValue.setName(constant.first);
            diagramValue.setValue(constant.second);
            containerToFill.getValues().add(diagramValue);
         }
      }
   }
   
   /**
    * Creates for the given {@link Pair}s {@link ODValue} or {@link ODAssociation}s.
    * @param heapObjectMap The {@link Map} which maps object name to {@link ODObject}s.
    * @param contentToAdd The {@link Pair}s to analyze.
    * @param containerToFill The {@link AbstractODValueContainer} to fill.
    * @param associations The {@link List} which contains all available {@link ODAssociation}s.
    */
   protected void createStateValuesAndAssociations(Map<Heap, Map<String, ODObject>> heapObjectMap, 
                                                   List<Pair<String, String>> contentToAdd, 
                                                   AbstractODValueContainer containerToFill, 
                                                   List<Pair<ODAssociation, AbstractODValueContainer>> associations) {
      for (Pair<String, String> constant : contentToAdd) {
         List<ODObject> diagramObjects = searchDiagramObjects(heapObjectMap, constant.second);
         if (!diagramObjects.isEmpty()) {
            for (ODObject diagramObject : diagramObjects) {
               ODAssociation diagramAssociation = ODFactory.eINSTANCE.createODAssociation();
               diagramAssociation.setName(constant.first);
               diagramAssociation.setTarget(diagramObject);
               containerToFill.getAssociations().add(diagramAssociation);
               associations.add(new Pair<ODAssociation, AbstractODValueContainer>(diagramAssociation, containerToFill));
            }
         }
         else {
            ODValue diagramValue = ODFactory.eINSTANCE.createODValue();
            diagramValue.setName(constant.first);
            diagramValue.setValue(constant.second);
            containerToFill.getValues().add(diagramValue);
         }
      }
   }
   
   /**
    * Searches all {@link ODObject}s in all {@link Heap}s with the given name.
    * @param heapObjectMap The {@link Map} which maps object name to {@link ODObject}s.
    * @param name The name of the {@link ODObject} to search.
    * @return The found {@link ODObject}s.
    */
   protected List<ODObject> searchDiagramObjects(Map<Heap, Map<String, ODObject>> heapObjectMap, String name) {
      List<ODObject> result = new LinkedList<ODObject>();
      for (Map<String, ODObject> objectMap : heapObjectMap.values()) {
         ODObject diagramObject = objectMap.get(name);
         if (diagramObject != null) {
            result.add(diagramObject);
         }
      }
      return result;
   }
}