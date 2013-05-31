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

package org.key_project.sed.ui.visualization.object_diagram.wizard;

import org.eclipse.core.resources.IFile;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * A new wizard to save existing Object Diagrams in an additional resource.
 * @author Martin Hentschel
 */
public class SaveAsObjectDiagramWizard extends AbstractObjectDiagramSaveAsWizard {
   /**
    * The {@link IDiagramTypeProvider} which contains the {@link Diagram} to save as.
    */
   private IDiagramTypeProvider diagramTypeProvider;
   
   /**
    * Constructor.
    * @param diagramTypeProvider The {@link IDiagramTypeProvider} which contains the {@link Diagram} to save as.
    */
   public SaveAsObjectDiagramWizard(IDiagramTypeProvider diagramTypeProvider) {
      this.diagramTypeProvider = diagramTypeProvider;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected String getInitialWindowTitle() {
      return "Save Object Diagram as";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getDiagramAndModelPageTitle() {
      return "Save Object Diagram as";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Diagram getDiagramToSave(String fileName) {
      return diagramTypeProvider.getDiagram();
   }

   /**
    * Opens the wizard.
    * @param parentShell The parent {@link Shell}.
    * @param diagramTypeProvider The {@link IDiagramTypeProvider} which contains the {@link Diagram} to save as.
    * @return The wizard result.
    */
   public static int openWizard(Shell parentShell, IDiagramTypeProvider diagramTypeProvider) {
      SaveAsObjectDiagramWizard wizard = new SaveAsObjectDiagramWizard(diagramTypeProvider);
      IFile file = diagramTypeProvider != null ? GraphitiUtil.getFile(diagramTypeProvider.getDiagram()) : null;
      wizard.init(PlatformUI.getWorkbench(), SWTUtil.createSelection(file));
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      return dialog.open();
   }
}