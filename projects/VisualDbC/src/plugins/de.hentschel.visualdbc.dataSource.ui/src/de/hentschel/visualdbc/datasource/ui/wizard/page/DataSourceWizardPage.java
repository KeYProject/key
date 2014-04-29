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

package de.hentschel.visualdbc.datasource.ui.wizard.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Map;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;

import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.ui.composite.DataSourceComposite;

/**
 * The wizard page with the data source settings.
 * @author Martin Hentschel
 */
public class DataSourceWizardPage extends WizardPage {
   /**
    * The {@link DataSourceComposite} to define connection settings.
    */
   private DataSourceComposite dsc;
   
   /**
    * The current {@link ISelection} that is used to compute the initial values.
    */
   private ISelection selection;

   /**
    * Constructor
    * @param pageName The name of the page.
    * @param selection The current {@link ISelection} that is used to compute the initial values.
    */
   public DataSourceWizardPage(String pageName, ISelection selection) {
      super(pageName);
      this.selection = selection;
      setTitle("Data Source");
      setDescription("Select a data source and define the settings.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      dsc = new DataSourceComposite(parent, SWT.NONE, selection);
      setControl(dsc);
      dsc.addPropertyChangeListener(DataSourceComposite.PROP_DRIVER, new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent evt) {
            handleDriverChanged();
         }
      });
      dsc.addPropertyChangeListener(DataSourceComposite.PROP_VALUES, new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent evt) {
            handleValuesChanged();
         }
      });
      updatePageCompleted();
   }

   /**
    * When a new connection settings were defined.
    */
   protected void handleValuesChanged() {
      updatePageCompleted();
   }

   /**
    * When a new data source was selected.
    */
   protected void handleDriverChanged() {
      updatePageCompleted();
   }
   
   /**
    * Updates the page completion state.
    */
   protected void updatePageCompleted() {
      IDSDriver driver = dsc.getDriver();
      if (driver != null) {
         String message = dsc.getSettingsValidationMessage();
         if (message != null) {
            setErrorMessage(message);
            setPageComplete(false);
         }
         else {
            setErrorMessage(null);
            setPageComplete(true);
         }
      }
      else {
         setErrorMessage("No data source selected.");
         setPageComplete(false);
      }
   }
   
   /**
    * Returns the selected {@link IDSDriver}.
    * @return The selected {@link IDSDriver}.
    */   
   public IDSDriver getDriver() {
      return dsc.getDriver();
   }
   
   /**
    * Returns the values for the selected driver.
    * @return The values for the selected driver.
    */   
   public Map<String, Object> getValues() {
      return dsc.getValues();
   }
}