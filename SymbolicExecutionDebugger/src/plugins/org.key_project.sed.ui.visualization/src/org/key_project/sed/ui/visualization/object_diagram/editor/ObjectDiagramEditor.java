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

package org.key_project.sed.ui.visualization.object_diagram.editor;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.CustomContext;
import org.eclipse.graphiti.ui.editor.DiagramBehavior;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.ui.visualization.object_diagram.feature.GenerateObjectDiagramFromSENodeCustomFeature;
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
    * Indicates that this editor is read-only or editable otherwise.
    */
   private boolean readOnly;
   
   /**
    * Constructor.
    */
   public ObjectDiagramEditor() {
      this(false);
   }
   
   /**
    * Constructor.
    * @param readOnly Indicates that this editor is read-only or editable otherwise.
    */
   public ObjectDiagramEditor(boolean readOnly) {
      setGlobalEnabled(true);
      setDefaultSelectionSynchronizationEnabled(false);
      this.readOnly = readOnly;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected DiagramBehavior createDiagramBehavior() {
      return new ObjectDiagramBehavior(this, readOnly);
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
    * Generates an object diagram for the given {@link ISENode}.
    * @param node The {@link ISENode} to generate object diagram for.
    * @throws DebugException Occurred Exception.
    */
   public void generateObjectDiagram(ISENode node) throws DebugException {
      if (node != null) {
         IDiagramTypeProvider typeProvider = getDiagramTypeProvider();
         IFeatureProvider featureProvider = typeProvider.getFeatureProvider();
         IFeature feature = new GenerateObjectDiagramFromSENodeCustomFeature(featureProvider);
         ICustomContext context = new CustomContext();
         context.putProperty(GenerateObjectDiagramFromSENodeCustomFeature.PROPERTY_NODE, node);
         executeFeatureInJob("Generating Object Diagram for \"" + StringUtil.toSingleLinedString(node.getName()) + "\"", feature, context);
      }
   }
}