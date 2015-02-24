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

package org.key_project.sed.ui.visualization.execution_tree.editor;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;
import org.eclipse.graphiti.ui.editor.DiagramBehavior;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeToolBehaviorProvider;
import org.key_project.sed.ui.visualization.execution_tree.wizard.SaveAsExecutionTreeDiagramWizard;
import org.key_project.sed.ui.visualization.util.PaletteHideableDiagramEditor;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

/**
 * {@link DiagramEditor} for Symbolic Execution Tree Diagrams.
 * @author Martin Hentschel
 */
// TODO: Reload diagram when the domain model file has changed.
public class ExecutionTreeDiagramEditor extends PaletteHideableDiagramEditor {
   /**
    * Indicates that this editor is read-only or editable otherwise.
    */
   private boolean readOnly;

   /**
    * Constructor.
    */
   public ExecutionTreeDiagramEditor() {
      this(false);
   }

   /**
    * Constructor.
    * @param readOnly Indicates that this editor is read-only or editable otherwise.
    */
   public ExecutionTreeDiagramEditor(boolean readOnly) {
      this.readOnly = readOnly;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected DiagramBehavior createDiagramBehavior() {
      return new ExecutionTreeDiagramBehavior(this, readOnly);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionTreeDiagramBehavior getDiagramBehavior() {
      return (ExecutionTreeDiagramBehavior)super.getDiagramBehavior();
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
      SaveAsExecutionTreeDiagramWizard.openWizard(getSite().getShell(), getDiagramTypeProvider());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void selectBusinessObjects(Object[] businessObjects) {
      ExecutionTreeToolBehaviorProvider behaviorProvider = getExecutionTreeToolBehaviorProvider();
      List<PictogramElement> pictogramElements = new LinkedList<PictogramElement>();
      for (Object bo : businessObjects) {
         PictogramElement[] referencingPes = getPictogramElements(bo);
         for (PictogramElement pe : referencingPes) {
            if (behaviorProvider == null || behaviorProvider.isSelectable(pe)) {
               pictogramElements.add(pe);
            }
         }
      }
      selectPictogramElements(pictogramElements.toArray(new PictogramElement[pictogramElements.size()]));
   }

   /**
    * Returns the used {@link ExecutionTreeToolBehaviorProvider} if available.
    * @return The {@link ExecutionTreeToolBehaviorProvider} or {@code null} if not available.
    */
   public ExecutionTreeToolBehaviorProvider getExecutionTreeToolBehaviorProvider() {
      IDiagramTypeProvider diagramProvider = getDiagramTypeProvider();
      if (diagramProvider != null) {
         IToolBehaviorProvider result = ArrayUtil.search(diagramProvider.getAvailableToolBehaviorProviders(), new IFilter<IToolBehaviorProvider>() {
            @Override
            public boolean select(IToolBehaviorProvider element) {
               return element instanceof ExecutionTreeToolBehaviorProvider;
            }
         });
         return (ExecutionTreeToolBehaviorProvider) result;
      }
      else {
         return null;
      }
   }
}