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

package de.hentschel.visualdbc.statistic.ui.wizard.page;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;

import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;

/**
 * {@link WizardPage} to select {@link DbCProofObligation}.
 * @author Martin Hentschel
 */
public class SelectProofObligationWizardPage extends WizardPage {
   /**
    * All available {@link DbCProofObligation}.
    */
   private List<DbcProofObligation> allObligations;

   /**
    * The selected {@link DbCProofObligation}s.
    */
   private List<DbcProofObligation> selectedObligations;
   
   /**
    * The {@link Table} that contains the available {@link DbCProofObligation}s.
    */
   private Table table;

   /**
    * Constructor.
    * @param pageName The name of the page.
    * @param allObligations All available {@link DbCProofObligation}.
    * @param selectedObligations The selected {@link DbCProofObligation}s.
    */
   public SelectProofObligationWizardPage(String pageName, List<DbcProofObligation> allObligations, List<DbcProofObligation> selectedObligations) {
      super(pageName);
      Assert.isNotNull(allObligations);
      Assert.isNotNull(selectedObligations);
      this.allObligations = allObligations;
      this.selectedObligations = selectedObligations;
      setTitle("Proof Obligations");
      setDescription("Select the proof obligations for the statistic.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite composite = new Composite(parent, SWT.NONE);
      composite.setLayout(new GridLayout());
      table = new Table(composite, SWT.BORDER | SWT.CHECK | SWT.MULTI);
      table.setLayoutData(new GridData(GridData.FILL_BOTH));
      for (DbcProofObligation obligation : allObligations) {
         TableItem item = new TableItem(table, SWT.NONE);
         item.setText(obligation.getObligation());
         item.setData(obligation);
         item.setChecked(selectedObligations.contains(obligation));
      }
      Composite buttonComposite = new Composite(composite, SWT.NONE);
      buttonComposite.setLayout(new GridLayout(2, true));
      Button selectAllButton = new Button(buttonComposite, SWT.PUSH);
      selectAllButton.setText("&Select All");
      selectAllButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      selectAllButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            selectAll();
         }
      });
      Button unselectAllButton = new Button(buttonComposite, SWT.PUSH);
      unselectAllButton.setText("&Deselect All");
      unselectAllButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      unselectAllButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            unselectAll();
         }
      });
      setControl(composite);
   }
   
   /**
    * Selects all proof obligations.
    */
   public void selectAll() {
      setSelectedStateInAllEntries(true);
   }

   /**
    * Deselects all proof obligations.
    */
   public void unselectAll() {
      setSelectedStateInAllEntries(false);
   }

   /**
    * Sets the selected state in all proof obligation.
    * @param selectedStateToSet The selected state to set.
    */
   protected void setSelectedStateInAllEntries(boolean selectedStateToSet) {
      for (TableItem item : table.getItems()) {
         item.setChecked(selectedStateToSet);
      }
   }

   /**
    * Returns the selected {@link DbCProofObligation}s.
    * @return The selected {@link DbCProofObligation}s.
    */
   public List<DbcProofObligation> getSelectedObligations() {
      List<DbcProofObligation> result = new LinkedList<DbcProofObligation>();
      for (TableItem item : table.getItems()) {
         if (item.getChecked()) {
            result.add((DbcProofObligation)item.getData());
         }
      }
      return result;
   }
}