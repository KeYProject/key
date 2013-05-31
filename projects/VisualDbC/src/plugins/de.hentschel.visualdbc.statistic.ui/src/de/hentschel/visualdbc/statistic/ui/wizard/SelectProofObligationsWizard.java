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

package de.hentschel.visualdbc.statistic.ui.wizard;

import java.util.List;

import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.widgets.Shell;

import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.statistic.ui.wizard.page.SelectProofObligationWizardPage;

/**
 * {@link Wizard} to select {@link DbCProofObligation}s.
 * @author Martin Hentschel
 */
public class SelectProofObligationsWizard extends Wizard {
   /**
    * All available {@link DbCProofObligation}.
    */
   private List<DbcProofObligation> allObligations;

   /**
    * The selected {@link DbCProofObligation}s.
    */
   private List<DbcProofObligation> selectedObligations;
   
   /**
    * The {@link WizardPage} that shows the available {@link DbCProofObligation}s.
    */
   private SelectProofObligationWizardPage selectProofObligationWizardPage;
   
   /**
    * Constructor.
    * @param allObligations All available {@link DbCProofObligation}.
    * @param selectedObligations The selected {@link DbCProofObligation}s.
    */
   public SelectProofObligationsWizard(List<DbcProofObligation> allObligations, List<DbcProofObligation> selectedObligations) {
      super();
      this.allObligations = allObligations;
      this.selectedObligations = selectedObligations;
      setWindowTitle("Proof Obligations");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      selectProofObligationWizardPage = new SelectProofObligationWizardPage("selectProofObligationWizardPage", allObligations, selectedObligations);
      addPage(selectProofObligationWizardPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      selectedObligations = selectProofObligationWizardPage.getSelectedObligations();
      return true;
   }
   
   /**
    * Returns the selected {@link DbCProofObligation}s.
    * @return The selected {@link DbCProofObligation}s.
    */
   public List<DbcProofObligation> getSelectedObligations() {
      return selectedObligations;
   }

   /**
    * Opens the {@link SelectProofObligationsWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell} to use.
    * @param allObligations All available {@link DbCProofObligation}.
    * @param selectedObligations The selected {@link DbCProofObligation}s.
    * @return The new selected {@link DbCProofObligation}s or {@code null} if the user cancels the wizard.
    */
   public static List<DbcProofObligation> open(Shell parentShell, List<DbcProofObligation> allObligations, List<DbcProofObligation> selectedObligations) {
      SelectProofObligationsWizard wizard = new SelectProofObligationsWizard(allObligations, selectedObligations);
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      dialog.setHelpAvailable(false);
      if (WizardDialog.OK == dialog.open()) {
         return wizard.getSelectedObligations();
      }
      else {
         return null;
      }
   }
}