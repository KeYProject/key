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

import org.eclipse.graphiti.ui.editor.DiagramBehavior;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.key_project.sed.ui.visualization.execution_tree.wizard.SaveAsExecutionTreeDiagramWizard;
import org.key_project.sed.ui.visualization.util.PaletteHideableDiagramEditor;

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
}