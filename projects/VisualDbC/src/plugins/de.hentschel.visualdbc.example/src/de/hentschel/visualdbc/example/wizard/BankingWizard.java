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

package de.hentschel.visualdbc.example.wizard;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;
import org.key_project.util.eclipse.BundleUtil;

import de.hentschel.visualdbc.example.Activator;

/**
 * Example wizard to create an java project that contains the banking example.
 * The banking example is extracted from this plug-in in the created java project.
 * After that the diagram file is opened and selected in project explorer.
 * @author Martin Hentschel
 */
public class BankingWizard extends AbstractExampleWizard {
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   protected boolean createExampleContent(IContainer sourceDirectory) throws Exception {
      // Create folder for package "banking"
      IFolder paycardPackage = ((IContainer) sourceDirectory).getFolder(new Path("banking"));
      if (!paycardPackage.exists()) {
         paycardPackage.create(true, true, null);
      }
      // Extract files from plug-in into folder "paycard"
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/Banking/banking", paycardPackage);
      // Update path from the key connection settings inside the model file
      updateLocationInModelFile(paycardPackage.getFile("Banking.dbc"), paycardPackage);
      // Search diagram file
      IFile diagramFile = paycardPackage.getFile("Banking.dbc_diagram");
      if (diagramFile != null && diagramFile.exists()) {
         // Select diagram file in project explorer
         selectAndReveal(diagramFile);
         // Open diagram file
         openResource(diagramFile);
      }
      return true;
   }

   /**
    * Opens the wizard in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell} to use.
    * @return The wizard result.
    */
   @SuppressWarnings("restriction")
   public static int openWizard(Shell parentShell) {
      BankingWizard wizard = new BankingWizard();
      wizard.init(PlatformUI.getWorkbench(), null);
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      return dialog.open();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getExampleName() {
      return "Banking Example";
   }
}