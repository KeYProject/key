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

package de.hentschel.visualdbc.datasource.ui.setting;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;
import de.hentschel.visualdbc.datasource.ui.setting.event.ISettingControlListener;
import de.hentschel.visualdbc.datasource.ui.util.SettingControlUtil;

/**
 * <p>
 * Creates control to edit connection values for an {@link IDSConnection}
 * that are represented by an {@link IDSConnectionSetting}.
 * </p>
 * <p>
 * Concrete implementations are registered by extension point
 * {@link SettingControlUtil#SETTING_CONTROL_EXTENSION_POINT}.
 * </p>
 * @author Martin Hentschel
 */
public interface ISettingControl {
   /**
    * Create the SWT {@link Control} that is shown in the UI and allows to edit the value.
    * @param parent The parent {@link Composite}.
    * @return The created {@link Control}.
    */
   public Control createControl(Composite parent);
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public Object getValue();
   
   /**
    * Returns the the validation message or {@code null} if the value is valid.
    * @return The validation message or {@code null} if the value is valid.
    */
   public String getValidationMessage();
   
   /**
    * Sets the value.
    * @param value The value to set.
    */
   public void setValue(Object value);
   
   /**
    * Ads the {@link ISettingControlListener}.
    * @param l The listener to add.
    */
   public void addSettingControlListener(ISettingControlListener l);
   
   /**
    * Removes the {@link ISettingControlListener}.
    * @param l The listener to remove.
    */
   public void removeSettingControlListener(ISettingControlListener l);
   
   /**
    * Returns all registered {@link ISettingControlListener}s.
    * @return The registered {@link ISettingControlListener}s.
    */
   public ISettingControlListener[] getSettingControlListeners();
}