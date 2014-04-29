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

package org.key_project.sed.ui.visualization.execution_tree.wizard;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.execution_tree.wizard.page.ModelFileSaveOptionsWizardPage;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * A new wizard to save existing Symbolic Execution Tree Diagrams in an additional resource.
 * @author Martin Hentschel
 */
public class SaveAsExecutionTreeDiagramWizard extends AbstractExecutionTreeDiagramSaveAsWizard {
   /**
    * The {@link IDiagramTypeProvider} which contains the {@link Diagram} to save as.
    */
   private IDiagramTypeProvider diagramTypeProvider;

   /**
    * Constructor.
    * @param diagramTypeProvider The {@link IDiagramTypeProvider} which contains the {@link Diagram} to save as.
    */
   public SaveAsExecutionTreeDiagramWizard(IDiagramTypeProvider diagramTypeProvider) {
      super();
      this.diagramTypeProvider = diagramTypeProvider;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ModelFileSaveOptionsWizardPage createModelFileSaveOptionsWizardPage(String pageName) {
      return new ModelFileSaveOptionsWizardPage(pageName);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugTarget[] getDebugTargetsToSave() {
      Assert.isNotNull(diagramTypeProvider);
      Assert.isNotNull(diagramTypeProvider.getFeatureProvider());
      return ExecutionTreeUtil.getAllDebugTargets(diagramTypeProvider);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Diagram getDiagramToSave() {
      Assert.isNotNull(diagramTypeProvider);
      Diagram diagram = diagramTypeProvider.getDiagram();
      return EcoreUtil.copy(diagram); // Return a copy because it is modified during save process (URL to domain file)
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getInitialWindowTitle() {
      return "Save Symbolic Execution Tree Diagram";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getDiagramPageTitle() {
      return "Save Symbolic Execution Tree Diagram";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getModelPageTitle() {
      return "Save Symbolic Execution Tree Domain Model";
   }
   
   /**
    * Opens the wizard.
    * @param parentShell The parent {@link Shell}.
    * @param diagramTypeProvider The {@link IDiagramTypeProvider} which contains the {@link Diagram} to save as.
    * @return The wizard result.
    */
   public static int openWizard(Shell parentShell, IDiagramTypeProvider diagramTypeProvider) {
      SaveAsExecutionTreeDiagramWizard wizard = new SaveAsExecutionTreeDiagramWizard(diagramTypeProvider);
      IFile file = diagramTypeProvider != null ? GraphitiUtil.getFile(diagramTypeProvider.getDiagram()) : null;
      wizard.init(PlatformUI.getWorkbench(), SWTUtil.createSelection(file));
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      return dialog.open();
   }
}