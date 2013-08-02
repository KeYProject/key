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

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.ui.setting.event.SettingControlEvent;

/**
 * Implementation of {@link ISettingControl} to select a {@link DSPackageManagement}.
 * @author Martin Hentschel
 */
public class PackageManagementControl extends AbstractSettingControl {
   /**
    * The control to select a {@link DSPackageManagement}.
    */
   private Combo control;
   
   /**
    * {@inheritDoc}
    */   
   @Override
   public Control createControl(Composite parent) {
      control = new Combo(parent, SWT.READ_ONLY);
      DSPackageManagement[] values = DSPackageManagement.values();
      for (DSPackageManagement value : values) {
         control.add(value.getDisplayText());
      }
      control.setText(DSPackageManagement.getDefault().getDisplayText());
      control.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleSelectionChanged();
         }
      });
      return control;
   }
   
   /**
    * When the selection has changed.
    */
   protected void handleSelectionChanged() {
      fireValueChanged(new SettingControlEvent(this, getValue(), getValidationMessage()));
   }   

   /**
    * {@inheritDoc}
    */   
   @Override
   public DSPackageManagement getValue() {
      int selectedIndex = control.getSelectionIndex();
      Assert.isTrue(selectedIndex >= 0 && selectedIndex < DSPackageManagement.values().length);
      return DSPackageManagement.values()[selectedIndex];
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public String getValidationMessage() {
      DSPackageManagement value = getValue();
      if (value == null) {
         return "No value selected.";
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public void setValue(Object value) {
      if (value instanceof DSPackageManagement) {
         control.setText(((DSPackageManagement)value).getDisplayText());
         handleSelectionChanged();
      }
   }
}