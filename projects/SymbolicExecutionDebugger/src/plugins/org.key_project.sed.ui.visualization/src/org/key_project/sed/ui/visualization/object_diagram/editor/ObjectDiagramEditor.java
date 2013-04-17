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

package org.key_project.sed.ui.visualization.object_diagram.editor;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.CustomContext;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.object_diagram.feature.GenerateObjectDiagramFromSEDNodeCustomFeature;
import org.key_project.sed.ui.visualization.object_diagram.wizard.SaveAsObjectDiagramWizard;
import org.key_project.sed.ui.visualization.util.PaletteHideableDiagramEditor;
import org.key_project.util.java.StringUtil;

/**
 * {@link DiagramEditor} for Object Diagrams.
 * @author Martin Hentschel
 */
public class ObjectDiagramEditor extends PaletteHideableDiagramEditor {
   /**
    * The ID of this editor.
    */
   public static final String EDITOR_ID = "org.key_project.sed.ui.visualization.ObjectDiagramEditor";
   
   /**
    * Constructor.
    */
   public ObjectDiagramEditor() {
      setGlobalEnabled(true);
      setDefaultSelectionSynchronizationEnabled(false);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isSaveAsAllowed() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void doSaveAs() {
      SaveAsObjectDiagramWizard.openWizard(getSite().getShell(), getDiagramTypeProvider());
   }
   
   /**
    * Generates an object diagram for the given {@link ISEDDebugNode}.
    * @param node The {@link ISEDDebugNode} to generate object diagram for.
    * @throws DebugException Occurred Exception.
    */
   public void generateObjectDiagram(ISEDDebugNode node) throws DebugException {
      if (node != null) {
         IDiagramTypeProvider typeProvider = getDiagramTypeProvider();
         IFeatureProvider featureProvider = typeProvider.getFeatureProvider();
         IFeature feature = new GenerateObjectDiagramFromSEDNodeCustomFeature(featureProvider);
         ICustomContext context = new CustomContext();
         context.putProperty(GenerateObjectDiagramFromSEDNodeCustomFeature.PROPERTY_NODE, node);
         executeFeatureInJob("Generating Object Diagram for \"" + StringUtil.toSingleLinedString(node.getName()) + "\"", feature, context);
      }
   }
}