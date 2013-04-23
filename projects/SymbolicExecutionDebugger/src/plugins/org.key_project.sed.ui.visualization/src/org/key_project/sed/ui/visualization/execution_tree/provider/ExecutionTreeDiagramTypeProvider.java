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

package org.key_project.sed.ui.visualization.execution_tree.provider;

import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.graphiti.dt.AbstractDiagramTypeProvider;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.notification.INotificationService;
import org.eclipse.graphiti.platform.IDiagramEditor;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLReader;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.ui.visualization.execution_tree.editor.ExecutionTreeDiagramEditor;
import org.key_project.sed.ui.visualization.execution_tree.service.SEDIndependenceSolver;
import org.key_project.sed.ui.visualization.execution_tree.service.SEDNotificationService;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * {@link IDiagramTypeProvider} specific implementation for execution tree diagrams.
 * @author Martin Hentschel
 */
// TODO: Refactor branch conditions as connection text
public class ExecutionTreeDiagramTypeProvider extends AbstractDiagramTypeProvider {
   /**
    * The ID of the diagram type provided by this {@link IDiagramTypeProvider}.
    */
   public static final String DIAGRAM_TYPE_ID = "org.key_project.sed.ui.graphiti.ExecutionTreeDiagramType";
   
   /**
    * The provider ID of this {@link IDiagramTypeProvider}.
    */
   public static final String PROVIDER_ID = "org.key_project.sed.ui.graphiti.ExecutionTreeDiagramTypeProvider";

   /**
    * The type name which is the unique identifier in diagrams.
    */
   public static final String TYPE = "symbolicExecutionTreeDiagram";
   
   /**
    * Contains the available {@link IToolBehaviorProvider}s which are instantiated
    * lazily via {@link #getAvailableToolBehaviorProviders()}.
    */
   private ExecutionTreeToolBehaviorProvider[] toolBehaviorProviders;
   
   /**
    * Contains the available {@link ISEDDebugTarget}s.
    */
   private List<ISEDDebugTarget> debugTargets = new LinkedList<ISEDDebugTarget>();
   
   /**
    * The used {@link INotificationService}.
    */
   private SEDNotificationService notificationService;
   
   /**
    * Constructor.
    */
   public ExecutionTreeDiagramTypeProvider() {
      setFeatureProvider(new ExecutionTreeFeatureProvider(this));
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionTreeFeatureProvider getFeatureProvider() {
      return (ExecutionTreeFeatureProvider)super.getFeatureProvider();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEDNotificationService getNotificationService() {
      if (notificationService == null) {
         notificationService = new SEDNotificationService(this);
      }
      return notificationService;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionTreeToolBehaviorProvider[] getAvailableToolBehaviorProviders() {
      if (toolBehaviorProviders == null) {
         toolBehaviorProviders = new ExecutionTreeToolBehaviorProvider[] {new ExecutionTreeToolBehaviorProvider(this)};
      }
      return toolBehaviorProviders;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(Diagram diagram, IDiagramEditor diagramEditor) {
      try {
         // Make sure that the editor is compatible with this diagram
         Assert.isTrue(diagramEditor instanceof ExecutionTreeDiagramEditor, "The diagram type " + TYPE + " must be used in ExecutionTreeDiagramEditor instances.");
         boolean readonly = ((ExecutionTreeDiagramEditor)diagramEditor).isReadOnly();
         getFeatureProvider().setReadOnly(readonly);
         for (ExecutionTreeToolBehaviorProvider behaviorProvider : getAvailableToolBehaviorProviders()) {
            behaviorProvider.setReadOnly(readonly);
         }
         // Initialize type provider
         super.init(diagram, diagramEditor);
         // Load domain model file
         IFeatureProvider featureProvider = getFeatureProvider();
         if(featureProvider instanceof ExecutionTreeFeatureProvider) {
            SEDIndependenceSolver solver = ((ExecutionTreeFeatureProvider)featureProvider).getSEDIndependenceSolver();
            // Open input stream to domain file
            InputStream in = ExecutionTreeUtil.readDomainFile(diagram);
            // Load domain file
            SEDXMLReader reader = new SEDXMLReader();
            debugTargets = reader.read(in);
            solver.init(debugTargets);
         }
      }
      catch (FileNotFoundException e) {
         // Nothing to do
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(null, e);
         throw new RuntimeException(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resourcesSaved(Diagram diagram, Resource[] savedResources) {
      try {
         // Super stuff
         super.resourcesSaved(diagram, savedResources);
         // Save domain file
         if (ObjectUtil.equals(getDiagram(), diagram)) {
            OutputStream out = ExecutionTreeUtil.writeDomainFile(diagram);
            SEDXMLWriter writer = new SEDXMLWriter();
            writer.write(getDebugTargets(), SEDXMLWriter.DEFAULT_ENCODING, out, false, false);
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         throw new RuntimeException(e);
      }
   }

   /**
    * Makes sure that at least one {@link ISEDDebugTarget} is available
    * via {@link #getDebugTargets()}.
    */
   public void makeSureThatDebugTargetIsAvailable() {
      if (debugTargets.isEmpty()) {
         SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(null);
         target.setName("Default Symbolic Debug Target");
         getFeatureProvider().link(getDiagram(), target);
         debugTargets.add(target);
      }
   }

   /**
    * Returns the available {@link ISEDDebugTarget}s.
    * @return The available {@link ISEDDebugTarget}s.
    */
   public ISEDDebugTarget[] getDebugTargets() {
      return debugTargets.toArray(new ISEDDebugTarget[debugTargets.size()]);
   }
}