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

package de.hentschel.visualdbc.datasource.key.model;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSDriver;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnectionSetting;

/**
 * Creates {@link IDSConnection} that analyze source code with KeY.
 * @author Martin Hentschel
 */
public class KeyDriver extends AbstractDSDriver {
   /**
    * The unique driver ID.
    */
   public static final String ID = "de.hentschel.visualdbc.dataSource.key";
   
   /**
    * <p>
    * The key for the settings that defines the location folder with the source code.
    * </p>
    * <p>
    * The value is an instance of {@link File}.
    * </p>
    */
   public static final String SETTING_LOCATION = "location";

   /**
    * <p>
    * The key for the settings that defines the skipping of library classes.
    * </p>
    * <p>
    * The value is an instance of {@link Boolean}.
    * </p>
    */
   public static final String SETTING_SKIP_LIBRARY_CLASSES = "skipLibraryClasses";

   /**
    * <p>
    * The key for the settings that defines the package management.
    * </p>
    * <p>
    * The value is an instance of {@link DSPackageManagement}.
    * </p>
    */   
   public static String SETTING_PACKAGE_MANAGEMENT = "packageManagement";
   
   /**
    * The lazy loaded connection settings.
    */
   private List<IDSConnectionSetting> connectionSettings;

   /**
    * {@inheritDoc}
    */
   @Override
   public int getPriority() {
      return 0;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      return ID;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "KeY";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSConnection createConnection() {
      return new KeyConnection(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSConnectionSetting> getConnectionSettings() {
      if (connectionSettings == null) { // Lazy loading
         connectionSettings = new LinkedList<IDSConnectionSetting>();
         connectionSettings.add(new MemoryConnectionSetting(SETTING_LOCATION, "Location", "de.hentschel.visualdbc.datasource.ui.setting.FileOrResourceJavaPackageSettingControl") {
            /**
             * {@inheritDoc}
             */
            @Override
            public Object getInitialValue(ISelection selection) {
                return getInitalLocationValue(selection);
            }
         });
         connectionSettings.add(new MemoryConnectionSetting(SETTING_SKIP_LIBRARY_CLASSES, "Skip library classes", "de.hentschel.visualdbc.datasource.ui.setting.YesNoSettingControl") {
            /**
             * {@inheritDoc}
             */
            @Override
            public Object getInitialValue(ISelection selection) {
                return getInitalSkipLibraryClassesValue(selection);
            }
         });
         connectionSettings.add(new MemoryConnectionSetting(SETTING_PACKAGE_MANAGEMENT, "Package Management", "de.hentschel.visualdbc.datasource.ui.setting.PackageManagementControl") {
            /**
             * {@inheritDoc}
             */
            @Override
            public Object getInitialValue(ISelection selection) {
                return getInitalPackageManagementValue(selection);
            }
         });
      }
      return connectionSettings;
   }

   /**
    * Returns the initial package management value.
    * @param selection The current {@link ISelection}.
    * @return The initial value.
    */   
   protected Object getInitalPackageManagementValue(ISelection selection) {
      return DSPackageManagement.getDefault();
   }

   /**
    * Returns the initial skip library classes value.
    * @param selection The current {@link ISelection}.
    * @return The initial value.
    */
   protected Object getInitalSkipLibraryClassesValue(ISelection selection) {
      return Boolean.TRUE;
   }

   /**
    * Returns the initial location value.
    * @param selection The current {@link ISelection}.
    * @return The initial value.
    */
   protected Object getInitalLocationValue(ISelection selection) {
      Object value = null;
      if (selection instanceof IStructuredSelection) {
         value = ((IStructuredSelection)selection).getFirstElement();
      }
      return value;
   }
}