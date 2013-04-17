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

package de.hentschel.visualdbc.datasource.ui.test.util;

import java.util.Map;

import org.eclipse.swt.widgets.Control;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.ui.composite.DataSourceComposite;
import de.hentschel.visualdbc.datasource.ui.composite.DataSourceSettingComposite;
import de.hentschel.visualdbc.datasource.ui.setting.ISettingControl;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public class TestDataSourceUIUtil {
   /**
    * Forbid instances.
    */
   private TestDataSourceUIUtil() {
   }
   
   /**
    * Thread save execution of {@link ISettingControl#getValidationMessage()}.
    * @param settingControl The {@link ISettingControl} to get validation message from.
    * @param control The created UI element.
    * @return The validation message.
    */
   public static String getValidationMessageThreadSave(final ISettingControl settingControl, 
                                                       Control control) {
      IRunnableWithResult<String> getRun = new AbstractRunnableWithResult<String>() {
         @Override
         public void run() {
            setResult(settingControl.getValidationMessage());
         }
      };
      control.getDisplay().syncExec(getRun);
      return getRun.getResult();
   }
   
   /**
    * Thread save execution of {@link ISettingControl#getValue()}.
    * @param settingControl The {@link ISettingControl} to get value from.
    * @param control The created UI element.
    * @return The value.
    */
   public static Object getValueThreadSave(final ISettingControl settingControl, Control control) {
      IRunnableWithResult<Object> getRun = new AbstractRunnableWithResult<Object>() {
         @Override
         public void run() {
            setResult(settingControl.getValue());
         }
      };
      control.getDisplay().syncExec(getRun);
      return getRun.getResult();
   }
   
   /**
    * Thread save execution of {@link ISettingControl#setValue(Object)}
    * @param settingControl The {@link ISettingControl} to set on.
    * @param control The created UI element.
    * @param value The value to set.
    */
   public static void setValueThreadSave(final ISettingControl settingControl, Control control, final Object value) {
      Runnable setRun = new Runnable() {
         @Override
         public void run() {
            settingControl.setValue(value);
         }
      };
      control.getDisplay().syncExec(setRun);
   }

   /**
    * Thread save execution of {@link DataSourceSettingComposite#getValidationMessage()}.
    * @param control The {@link DataSourceSettingComposite} to read from.
    * @return The validation message.
    */
   public static Object getValidationMessageThreadSave(final DataSourceSettingComposite control) {
      IRunnableWithResult<String> getRun = new AbstractRunnableWithResult<String>() {
         @Override
         public void run() {
            setResult(control.getValidationMessage());
         }
      };
      control.getDisplay().syncExec(getRun);
      return getRun.getResult();
   }

   /**
    * Thread save execution of {@link DataSourceSettingComposite#getValues()}.
    * @param control The {@link DataSourceSettingComposite} to read from.
    * @return The values.
    */
   public static Map<String, Object> getValuesThreadSave(final DataSourceSettingComposite control) {
      IRunnableWithResult<Map<String, Object>> getRun = new AbstractRunnableWithResult<Map<String, Object>>() {
         @Override
         public void run() {
            setResult(control.getValues());
         }
      };
      control.getDisplay().syncExec(getRun);
      return getRun.getResult();
   }
   
   /**
    * Thread save execution of {@link DataSourceComposite#getDriver()}.
    * @param control The {@link DataSourceComposite} to read from.
    * @return The driver.
    */
   public static IDSDriver getDriverThreadSave(final DataSourceComposite control) {
      IRunnableWithResult<IDSDriver> getRun = new AbstractRunnableWithResult<IDSDriver>() {
         @Override
         public void run() {
            setResult(control.getDriver());
         }
      };
      control.getDisplay().syncExec(getRun);
      return getRun.getResult();
   }

   /**
    * Thread save execution of {@link DataSourceComposite#getSettingsValidationMessage()}.
    * @param control The {@link DataSourceComposite} to read from.
    * @return The validation message.
    */   
   public static String getSettingsValidationMessageThreadSave(final DataSourceComposite control) {
      IRunnableWithResult<String> getRun = new AbstractRunnableWithResult<String>() {
         @Override
         public void run() {
            setResult(control.getSettingsValidationMessage());
         }
      };
      control.getDisplay().syncExec(getRun);
      return getRun.getResult();
   }

   /**
    * Thread save execution of {@link DataSourceComposite#getValues()}.
    * @param control The {@link DataSourceComposite} to read from.
    * @return The values.
    */
   public static Map<String, Object> getValuesThreadSave(final DataSourceComposite control) {
      IRunnableWithResult<Map<String, Object>> getRun = new AbstractRunnableWithResult<Map<String, Object>>() {
         @Override
         public void run() {
            setResult(control.getValues());
         }
      };
      control.getDisplay().syncExec(getRun);
      return getRun.getResult();
   }
}