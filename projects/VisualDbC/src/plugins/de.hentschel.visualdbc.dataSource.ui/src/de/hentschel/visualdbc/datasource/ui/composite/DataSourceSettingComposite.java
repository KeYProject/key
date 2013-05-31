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

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;

import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;
import de.hentschel.visualdbc.datasource.ui.composite.event.DataSourceSettingCompositeEvent;
import de.hentschel.visualdbc.datasource.ui.composite.event.IDataSourceSettingCompositeListener;
import de.hentschel.visualdbc.datasource.ui.setting.ISettingControl;
import de.hentschel.visualdbc.datasource.ui.setting.event.ISettingControlListener;
import de.hentschel.visualdbc.datasource.ui.setting.event.SettingControlEvent;
import de.hentschel.visualdbc.datasource.ui.util.SettingControlUtil;

/**
 * Control to select a data source and to define the settings.
 * @author Martin Hentschel
 */
public class DataSourceSettingComposite extends Composite {
   /**
    * Contains all listeners.
    */
   private List<IDataSourceSettingCompositeListener> listeners = new LinkedList<IDataSourceSettingCompositeListener>();
   
   /**
    * Contains all contained {@link ISettingControl}s.
    */
   private Map<IDSConnectionSetting, ISettingControl> settingControls = new HashMap<IDSConnectionSetting, ISettingControl>();
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style.
    * @param connectionSettings The {@link IDSConnectionSetting} to edit.
    * @param selection The current {@link ISelection} that is used to compute the initial values.
    */
   public DataSourceSettingComposite(Composite parent, 
                                     int style, 
                                     List<IDSConnectionSetting> connectionSettings,
                                     ISelection selection) {
      super(parent, style);
      Assert.isNotNull(connectionSettings);
      setLayout(new GridLayout(2, false));
      for (IDSConnectionSetting cs : connectionSettings) {
         Label label = new Label(this, SWT.NONE);
         label.setLayoutData(new GridData(GridData.BEGINNING, GridData.BEGINNING, false, false));
         label.setText(cs.getName());
         ISettingControl sc = SettingControlUtil.createSettingControl(cs.getControlId());
         settingControls.put(cs, sc);
         Assert.isNotNull(sc, "No control created for setting control ID \"" + cs.getControlId() + "\".");
         Control control = sc.createControl(this);
         control.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         sc.addSettingControlListener(new ISettingControlListener() {
            @Override
            public void valueChanged(SettingControlEvent e) {
               handleValueChanged(e);
            }
         });
         sc.setValue(cs.getInitialValue(selection));
      }
   }
   
   /**
    * Returns all defined values.
    * @return The defined values.
    */
   public Map<String, Object> getValues() {
      Map<String, Object> values = new HashMap<String, Object>();
      for (Entry<IDSConnectionSetting, ISettingControl> entry : settingControls.entrySet()) {
         Assert.isNotNull(entry.getKey());
         Assert.isNotNull(entry.getKey().getKey());
         Assert.isNotNull(entry.getValue());
         values.put(entry.getKey().getKey(), entry.getValue().getValue());
      }
      return values;
   }
   
   /**
    * When a value in one of the {@link ISettingControl}s has changed.
    * @param e The event.
    */
   protected void handleValueChanged(SettingControlEvent e) {
      fireSettingValueChanged(new DataSourceSettingCompositeEvent(this, e.getSource(), e.getNewValue(), e.getValidationMessage()));
   }
   
   /**
    * Returns the the validation message for all child controls or {@code null} if everything is valid
    * @return The validation message or {@code null} if everything is valid.
    */
   public String getValidationMessage() {
      String validationMessage = null;
      Iterator<Entry<IDSConnectionSetting, ISettingControl>> controlIter = settingControls.entrySet().iterator();
      while (validationMessage == null && controlIter.hasNext()) {
         Entry<IDSConnectionSetting, ISettingControl> next = controlIter.next();
         String message = next.getValue().getValidationMessage();
         if (message != null) {
            validationMessage = next.getKey().getName() + ": " + message;
         }
      }
      return validationMessage;
   }

   /**
    * Fires the setting value change event to all listeners.
    * @param e The event to fire.
    */
   protected void fireSettingValueChanged(DataSourceSettingCompositeEvent e) {
      IDataSourceSettingCompositeListener[] allListeners = getDataSourceSettingCompositeListeners();
      for (IDataSourceSettingCompositeListener l : allListeners) {
         l.settingValueChanged(e);
      }
   }
   
   /**
    * Adds the listener.
    * @param l The listener to add.
    */
   public void addDataSourceSettingCompositeListener(IDataSourceSettingCompositeListener l) {
      if (l != null) {
         listeners.add(l);
      }
   }

   /**
    * Removes the listener.
    * @param l The listener to remove.
    */
   public void removeDataSourceSettingCompositeListener(IDataSourceSettingCompositeListener l) {
      if (l != null) {
         listeners.remove(l);
      }
   }

   /**
    * Returns all listeners.
    * @return All registered listeners.
    */
   public IDataSourceSettingCompositeListener[] getDataSourceSettingCompositeListeners() {
      return listeners.toArray(new IDataSourceSettingCompositeListener[listeners.size()]);
   }
}