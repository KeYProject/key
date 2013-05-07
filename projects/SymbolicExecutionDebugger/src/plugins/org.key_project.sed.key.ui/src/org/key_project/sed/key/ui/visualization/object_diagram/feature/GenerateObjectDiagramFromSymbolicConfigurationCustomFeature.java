/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
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
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicConfiguration;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicState;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;

/**
 * An {@link ICustomFeature} that generates an object diagram based
 * on the state provided via an {@link ISymbolicConfiguration}.
 * The {@link ISymbolicConfiguration} is specified via property {@link #PROPERTY_SYMBOLIC_CONFIGURATION} 
 * of the given {@link ICustomContext}.
 * @author Martin Hentschel
 */
public class GenerateObjectDiagramFromSymbolicConfigurationCustomFeature extends AbstractGenerateObjectDiagramCustomFeature {
   /**
    * Property for an {@link ISymbolicConfiguration} instance which provides
    * the state to visualize as object diagram.
    */
   public static final String PROPERTY_SYMBOLIC_CONFIGURATION = "symbolicConfiguration";
   
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public GenerateObjectDiagramFromSymbolicConfigurationCustomFeature(IFeatureProvider fp) {
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
      ISymbolicConfiguration configuration = null;
      Object contextNode = context.getProperty(PROPERTY_SYMBOLIC_CONFIGURATION);
      if (contextNode instanceof ISymbolicConfiguration) {
         configuration = (ISymbolicConfiguration)contextNode;
      }
      // Generate model and diagram if possible
      try {
         if (configuration != null) {
            // Get model
            ODModel model = ObjectDiagramUtil.getModel(getDiagram());
            // Clean diagram
            cleanModel(model);
            // Create new model
            PictogramElement statePE = createModelAndDiagram(model, configuration, monitor);
            // Improve diagram layout
            improveLayout(model, monitor);
            // Select statePE
            GraphitiUtil.select(getFeatureProvider(), statePE);
         }
      }
      catch (OperationCanceledException e) {
         // Nothing to do.
      }
      finally {
         monitor.done();
      }
   }

   /**
    * Creates the model and diagram.
    * @param model The {@link ODModel} to fill.
    * @param configuration The {@link ISymbolicConfiguration} to show.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The created {@link PictogramElement} of the root {@link ODState}.
    */
   protected PictogramElement createModelAndDiagram(ODModel model, ISymbolicConfiguration configuration, IProgressMonitor monitor) {
      if (configuration != null) {
         // Create state
         ODState state = createState(configuration.getState());
         PictogramElement statePE = null;
         if (state != null) {
            model.getStates().add(state);
            statePE = addNodeToDiagram(state, 0, 0);
         }
         // Create objects
         Map<ISymbolicObject, ODObject> objectMapping = new HashMap<ISymbolicObject, ODObject>();
         Map<ISymbolicObject, PictogramElement> objectPEMapping = new HashMap<ISymbolicObject, PictogramElement>();
         for (ISymbolicObject symbolicObject : configuration.getObjects()) {
            ODObject object = createObject(symbolicObject);
            if (object != null) {
               model.getObjects().add(object);
               objectMapping.put(symbolicObject, object);
               PictogramElement objectPE = addNodeToDiagram(object, 0, 0);
               objectPEMapping.put(symbolicObject, objectPE);
            }
         }
         // Create associations
         if (state != null) {
            fillValueContainerWithAssociations(state, statePE, configuration.getState().getAssociations(), objectMapping, objectPEMapping);
         }
         for (ISymbolicObject symbolicObject : configuration.getObjects()) {
            ODObject object = objectMapping.get(symbolicObject);
            Assert.isNotNull(object);
            PictogramElement objectPE = objectPEMapping.get(symbolicObject);
            Assert.isNotNull(objectPE);
            fillValueContainerWithAssociations(object, objectPE, symbolicObject.getAssociations(), objectMapping, objectPEMapping);
         }
         return statePE;
      }
      else {
         return null;
      }
   }

   /**
    * Creates the {@link ODState} instance for the given {@link ISymbolicState}.
    * @param symbolicAssociation The given {@link ISymbolicState}.
    * @return The created {@link ODState}.
    */
   protected ODState createState(ISymbolicState symbolicState) {
      if (symbolicState != null) {
         ODState state = ODFactory.eINSTANCE.createODState();
         state.setName(symbolicState.getName());
         for (ISymbolicValue symbolicValue : symbolicState.getValues()) {
            ODValue value = createValue(symbolicValue);
            if (value != null) {
               state.getValues().add(value);
            }
         }
         return state;
      }
      else {
         return null;
      }
   }
   
   /**
    * Creates the {@link ODObject} instance for the given {@link ISymbolicObject}.
    * @param symbolicAssociation The given {@link ISymbolicObject}.
    * @return The created {@link ODObject}.
    */
   protected ODObject createObject(ISymbolicObject symbolicObject) {
      if (symbolicObject != null) {
         ODObject object = ODFactory.eINSTANCE.createODObject();
         object.setName(symbolicObject.getNameString());
         object.setType(symbolicObject.getTypeString());
         for (ISymbolicValue symbolicValue : symbolicObject.getValues()) {
            ODValue value = createValue(symbolicValue);
            if (value != null) {
               object.getValues().add(value);
            }
         }
         return object;
      }
      else {
         return null;
      }
   }
   
   /**
    * Creates the {@link ODValue} instance for the given {@link ISymbolicValue}.
    * @param symbolicAssociation The given {@link ISymbolicValue}.
    * @return The created {@link ODValue}.
    */
   protected ODValue createValue(ISymbolicValue symbolicValue) {
      if (symbolicValue != null) {
         ODValue value = ODFactory.eINSTANCE.createODValue();
         value.setName(symbolicValue.getName());
         value.setType(symbolicValue.getTypeString());
         value.setValue(symbolicValue.getValueString());
         return value;
      }
      else {
         return null;
      }
   }

   /**
    * Fills the given {@link AbstractODValueContainer} with associations.
    * @param container The {@link AbstractODValueContainer} to fill.
    * @param containerPE The {@link PictogramElement} of the container to fill.
    * @param associations The {@link ISymbolicAssociation} to add.
    * @param objectMapping The object mapping to use.
    * @param objectPEMapping The object {@link PictogramElement}s mapping to use.
    */
   protected void fillValueContainerWithAssociations(AbstractODValueContainer container,
                                                     PictogramElement containerPE,
                                                     ImmutableList<ISymbolicAssociation> associations, 
                                                     Map<ISymbolicObject, ODObject> objectMapping,
                                                     Map<ISymbolicObject, PictogramElement> objectPEMapping) {
      for (ISymbolicAssociation symbolicAssociation : associations) {
         ODAssociation association = createAssociation(symbolicAssociation, objectMapping);
         if (association != null) {
            container.getAssociations().add(association);
            PictogramElement targetPE = objectPEMapping.get(symbolicAssociation.getTarget());
            Assert.isNotNull(targetPE, "Symbolic model is inconsistent.");
            addConnectionToDiagram(association, containerPE, targetPE);
         }
      }
   }

   /**
    * Creates the {@link ODAssociation} instance for the given {@link ISymbolicAssociation}.
    * @param symbolicAssociation The given {@link ISymbolicAssociation}.
    * @param objectMapping The object mapping to use.
    * @return The created {@link ODAssociation}.
    */
   protected ODAssociation createAssociation(ISymbolicAssociation symbolicAssociation, 
                                             Map<ISymbolicObject, ODObject> objectMapping) {
      if (symbolicAssociation != null) {
         ODAssociation association = ODFactory.eINSTANCE.createODAssociation();
         association.setName(symbolicAssociation.getName());
         ODObject target = objectMapping.get(symbolicAssociation.getTarget());
         Assert.isNotNull(target, "Symbolic model is inconsistent.");
         association.setTarget(target);
         return association;
      }
      else {
         return null;
      }
   }
}