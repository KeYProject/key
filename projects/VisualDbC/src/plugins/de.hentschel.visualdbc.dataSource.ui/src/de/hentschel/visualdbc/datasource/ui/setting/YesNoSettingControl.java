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

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

import de.hentschel.visualdbc.datasource.ui.setting.event.SettingControlEvent;

/**
 * Implementation of {@link ISettingControl} to define a {@link Boolean} value
 * via a combo box that allows only "yes" and "no".
 * @author Martin Hentschel
 */
public class YesNoSettingControl extends AbstractSettingControl {
   /**
    * Text that is shown to select the "true" value.
    */
   public static final String ITEM_YES = "Yes";

   /**
    * Text that is shown to select the "false" value.
    */
   public static final String ITEM_NO = "No";
   
   /**
    * The selection control.
    */
   private Combo combo;

   /**
    * {@inheritDoc}
    */
   @Override
   public Control createControl(Composite parent) {
      combo = new Combo(parent, SWT.READ_ONLY);
      combo.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleSelectionChanged();
         }
      });
      combo.add(ITEM_YES);
      combo.add(ITEM_NO);
      combo.setText(ITEM_NO);
      return combo;
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
   public Object getValue() {
      return ITEM_YES.equals(combo.getText());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setValue(Object value) {
      if (value instanceof Boolean) {
         if (((Boolean)value).booleanValue()) {
            combo.setText(ITEM_YES);
         }
         else {
            combo.setText(ITEM_NO);
         }
         handleSelectionChanged();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getValidationMessage() {
      return null;
   }
}