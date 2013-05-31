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
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

import de.hentschel.visualdbc.datasource.ui.setting.event.SettingControlEvent;

/**
 * Implementation of {@link ISettingControl} to define a {@link Boolean} value.
 * @author Martin Hentschel
 */
public class BooleanSettingControl extends AbstractSettingControl {
   /**
    * The selection control.
    */
   private Button button;

   /**
    * {@inheritDoc}
    */
   @Override
   public Control createControl(Composite parent) {
      button = new Button(parent, SWT.CHECK);
      button.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleSelectionChanged();
         }
      });
      return button;
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
      return Boolean.valueOf(button.getSelection());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setValue(Object value) {
      if (value instanceof Boolean) {
         button.setSelection(((Boolean)value).booleanValue());
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