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

package de.hentschel.visualdbc.datasource.ui.composite;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;

import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.ui.composite.event.DataSourceSettingCompositeEvent;
import de.hentschel.visualdbc.datasource.ui.composite.event.IDataSourceSettingCompositeListener;
import de.hentschel.visualdbc.datasource.util.DriverUtil;

/**
 * Control to select a data source and to define the settings.
 * @author Martin Hentschel
 */
public class DataSourceComposite extends Composite {
   /**
    * Property for {@link #getDriver()}.
    */
   public static final String PROP_DRIVER = "driver";
   
   /**
    * Property for {@link #getValues()}.
    */
   public static final String PROP_VALUES = "values";
   
   /**
    * Manages {@link PropertyChangeListener}s.
    */
   private PropertyChangeSupport pcs = new PropertyChangeSupport(this);
   
   /**
    * <p>
    * Control to select a data source.
    * </p>
    * <p>
    * The selected index is equal to the index in {@link #drivers}.
    * </p>
    */
   private Combo dataSourceCombo;
   
   /**
    * All available {@link IDSDriver}s.
    */
   private List<IDSDriver> drivers;
   
   /**
    * All available {@link DataSourceSettingComposite}s.
    */
   private List<DataSourceSettingComposite> settingComposites;
   
   /**
    * Layout of {@link #settingsGroup}.
    */
   private StackLayout settingsGroupLayout;
   
   /**
    * Shows the {@link DataSourceSettingComposite} for the selected {@link IDSDriver}.
    */
   private Group settingsGroup;
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style.
    * @param selection The current {@link ISelection} that is used to compute the initial values.
    */
   public DataSourceComposite(Composite parent, int style, ISelection selection) {
      super(parent, style);
      setLayout(new GridLayout(1, false));
      Composite dataSourceComposite = new Composite(this, SWT.NONE);
      dataSourceComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      dataSourceComposite.setLayout(new GridLayout(2, false));
      Label dataSourceLabel = new Label(dataSourceComposite, SWT.NONE);
      dataSourceLabel.setText("&Data Source");
      dataSourceCombo = new Combo(dataSourceComposite, SWT.READ_ONLY);
      dataSourceCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      dataSourceCombo.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            changeConnectionSettings();
         }
      });
      settingsGroup = new Group(this, SWT.NONE);
      settingsGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
      settingsGroup.setText("Settings");
      settingsGroupLayout = new StackLayout(); 
      settingsGroup.setLayout(settingsGroupLayout);
      // Initialize data sources
      addDataSources(selection);
      changeConnectionSettings();
   }
   
   /**
    * Adds the listener for the defined property.
    * @param propertyName The property to observe.
    * @param listener The listener to add.
    */
   public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
      pcs.addPropertyChangeListener(propertyName, listener);
   }
   
   /**
    * Removes the listener from the property.
    * @param propertyName The observed property.
    * @param listener The listener to remove.
    */
   public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
      pcs.removePropertyChangeListener(propertyName, listener);
   }
   
   /**
    * Returns all listeners for that property.
    * @param propertyName The observed property.
    * @return All registered listener.
    */
   public PropertyChangeListener[] getPropertyChangeListeners(String propertyName) {
      return pcs.getPropertyChangeListeners(propertyName);
   }
   
   /**
    * Changes the {@link DataSourceSettingComposite} to the one of 
    * the currently selected {@link IDSDriver}.
    */
   protected void changeConnectionSettings() {
      if (!settingComposites.isEmpty()) {
         int selectedIndex = dataSourceCombo.getSelectionIndex();
         Assert.isTrue(selectedIndex >= 0 && selectedIndex < settingComposites.size());
         DataSourceSettingComposite dssc = settingComposites.get(selectedIndex);
         settingsGroupLayout.topControl = dssc;
         settingsGroup.layout();
      }
      pcs.firePropertyChange(PROP_DRIVER, null, getDriver());
   }

   /**
    * Adds the available {@link IDSDriver} to {@link #dataSourceCombo}.
    * @param selection The current {@link ISelection} that is used to compute the initial values.
    */
   protected void addDataSources(ISelection selection) {
      drivers = DriverUtil.getDrivers();
      settingComposites = new LinkedList<DataSourceSettingComposite>();
      boolean driverSelected = false;
      for (IDSDriver driver : drivers) {
         dataSourceCombo.add(driver.getName());
         if (!driverSelected) {
            dataSourceCombo.setText(driver.getName());
            driverSelected = true;
         }
         DataSourceSettingComposite dssc = new DataSourceSettingComposite(settingsGroup, SWT.NONE, driver.getConnectionSettings(), selection);
         settingComposites.add(dssc);
         dssc.addDataSourceSettingCompositeListener(new IDataSourceSettingCompositeListener() {
            @Override
            public void settingValueChanged(DataSourceSettingCompositeEvent e) {
               handleSettingValueChanged(e);
            }
         });
      }
   }

   /**
    * When a value in one of the {@link DataSourceSettingComposite}s has changed.
    * @param e The event.
    */
   protected void handleSettingValueChanged(DataSourceSettingCompositeEvent e) {
      pcs.firePropertyChange(PROP_VALUES, null, getValues());
   }
   
   /**
    * Returns the selected {@link IDSDriver}.
    * @return The selected {@link IDSDriver}.
    */
   public IDSDriver getDriver() {
      if (!settingComposites.isEmpty()) {
         int selectedIndex = dataSourceCombo.getSelectionIndex();
         Assert.isTrue(selectedIndex >= 0 && selectedIndex < settingComposites.size());
         return drivers.get(selectedIndex);
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the values for the selected driver.
    * @return The values for the selected driver.
    */
   public Map<String, Object> getValues() {
      if (!settingComposites.isEmpty()) {
         int selectedIndex = dataSourceCombo.getSelectionIndex();
         Assert.isTrue(selectedIndex >= 0 && selectedIndex < settingComposites.size());
         return settingComposites.get(selectedIndex).getValues();
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the the validation message for the current settings.
    * @return The validation message or {@code null} if everything is valid.
    */
   public String getSettingsValidationMessage() {
      if (!settingComposites.isEmpty()) {
         int selectedIndex = dataSourceCombo.getSelectionIndex();
         Assert.isTrue(selectedIndex >= 0 && selectedIndex < settingComposites.size());
         return settingComposites.get(selectedIndex).getValidationMessage();
      }
      else {
         return null;
      }
   }
}