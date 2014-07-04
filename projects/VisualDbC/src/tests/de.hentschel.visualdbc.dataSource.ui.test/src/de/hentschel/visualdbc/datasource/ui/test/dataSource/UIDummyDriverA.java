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

package de.hentschel.visualdbc.datasource.ui.test.dataSource;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSDriver;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnection;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnectionSetting;

/**
 * A dummy driver that provides some setting controls.
 * @author Martin Hentschel
 */
public class UIDummyDriverA extends AbstractDSDriver {
   /**
    * The key of setting: Boolean
    */
   public static final String SETTING_BOOLEAN = "boolean";

   /**
    * The key of setting: Resource Package
    */
   public static final String SETTING_RESOURCE_PACKAGE = "resourcePackage";
   
   /**
    * Indicates to initialize settings with valid values.
    */
   private static boolean initializeValidSettings = true;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSConnectionSetting> getConnectionSettings() {
      List<IDSConnectionSetting> result = new LinkedList<IDSConnectionSetting>();
      result.add(new MemoryConnectionSetting(SETTING_BOOLEAN, getBooleanLabelName(), "de.hentschel.visualdbc.datasource.ui.setting.BooleanSettingControl") {
         @Override
         public Object getInitialValue(ISelection selection) {
            return Boolean.TRUE;
         }
      });
      result.add(new MemoryConnectionSetting(SETTING_RESOURCE_PACKAGE, "Resource Package", "de.hentschel.visualdbc.datasource.ui.setting.FileOrResourceJavaPackageSettingControl") {
         @Override
         public Object getInitialValue(ISelection selection) {
            if (isInitializeValidSettings()) {
               return selection instanceof IStructuredSelection ? ((IStructuredSelection)selection).getFirstElement() : null;
            }
            else {
               return null;
            }
         }
      });
      return result;
   }
   
   /**
    * Returns the name of the boolean label.
    * @return The boolean label name.
    */
   public String getBooleanLabelName() {
      return "Boolean from " + getName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getPriority() {
      return Integer.MAX_VALUE;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      return getClass().getCanonicalName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "A-Dummy-Driver";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSConnection createConnection() throws DSException {
      return new MemoryConnection(this);
   }

   /**
    * Checks if the settings are initialized with valid values or not.
    * @return {@code true} = valid values, {@code false} one invalid value.
    */
   public static boolean isInitializeValidSettings() {
      return initializeValidSettings;
   }

   /**
    * Defines if the settings are initialized with valid values or not.
    * @param initializeValidSettings {@code true} = valid values, {@code false} one invalid value.
    */
   public static void setInitializeValidSettings(boolean initializeValidSettings) {
      UIDummyDriverA.initializeValidSettings = initializeValidSettings;
   }
}