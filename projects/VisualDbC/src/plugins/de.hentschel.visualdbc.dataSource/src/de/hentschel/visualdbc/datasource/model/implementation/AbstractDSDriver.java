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

package de.hentschel.visualdbc.datasource.model.implementation;

import java.io.File;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.hentschel.visualdbc.datasource.model.DSPackageManagement;
import de.hentschel.visualdbc.datasource.model.IDSDriver;

/**
 * Provides a basic implementation of an {@link IDSDriver}.
 * @author Martin Hentschel
 */
public abstract class AbstractDSDriver implements IDSDriver {
   /**
    * The suffix that is used to define the type.
    */
   public static final String TYPE_SUFFIX = "Type";
   
   /**
    * The type that is used to store {@link File}s.
    */
   public static final String TYPE_FILE = File.class.getName();
   
   /**
    * The type that is used to store {@link IPath}s.
    */
   public static final String TYPE_PATH = IPath.class.getName();
   
   /**
    * The type that is used to store {@link Boolean}s.
    */
   public static final String TYPE_BOOLEAN = Boolean.class.getName();
   
   /**
    * The type that is used to store {@link DSPackageManagement}s.
    */
   public static final String TYPE_DS_PACKAGE_MANAGEMENT = DSPackageManagement.class.getName();

   /**
    * {@inheritDoc}
    */
   @Override
   public Properties toPersistentProperties(Map<String, Object> connectionSettings) {
      Properties result = new Properties();
      if (connectionSettings != null) {
         Set<Entry<String, Object>> entries = connectionSettings.entrySet();
         for (Entry<String, Object> entry : entries) {
            checkTypeProperty(connectionSettings, entry.getKey());
            if (entry.getValue() instanceof Boolean) {
               addPersistentBooleanProperty(connectionSettings, result, entry.getKey(), (Boolean)entry.getValue());
            }
            else if (entry.getValue() instanceof DSPackageManagement) {
               addPersistentPackageManagementProperty(connectionSettings, result, entry.getKey(), (DSPackageManagement)entry.getValue());
            }
            else if (entry.getValue() instanceof File) {
               addPersistentFileProperty(connectionSettings, result, entry.getKey(), (File)entry.getValue());
            }
            else if (entry.getValue() instanceof Path) {
               addPersistentPathProperty(connectionSettings, result, entry.getKey(), (Path)entry.getValue());
            }
            else {
               throw new IllegalArgumentException("Unsupported connection value \"" + entry.getValue() + "\" in key \"" + entry.getKey() + "\".");
            }
         }
      }
      return result;
   }

   /**
    * Adds the {@link Path} property to the persistent properties. 
    * @param connectionSettings All connection settings.
    * @param persistentSettingsToFill The persistent properties to fill.
    * @param key The current key to convert.
    * @param value The value to convert.
    */
   protected void addPersistentPathProperty(Map<String, Object> connectionSettings, 
                                            Properties persistentSettingsToFill,
                                            String key, 
                                            Path value) {
      persistentSettingsToFill.setProperty(key, value.toString());
      persistentSettingsToFill.setProperty(key + TYPE_SUFFIX, TYPE_PATH);
   }

   /**
    * Adds the {@link File} property to the persistent properties. 
    * @param connectionSettings All connection settings.
    * @param persistentSettingsToFill The persistent properties to fill.
    * @param key The current key to convert.
    * @param value The value to convert.
    */
   protected void addPersistentFileProperty(Map<String, Object> connectionSettings, 
                                            Properties persistentSettingsToFill,
                                            String key, 
                                            File value) {
      persistentSettingsToFill.setProperty(key, value.toString());
      persistentSettingsToFill.setProperty(key + TYPE_SUFFIX, TYPE_FILE);
   }

   /**
    * Adds the {@link DSPackageManagement} property to the persistent properties. 
    * @param connectionSettings All connection settings.
    * @param persistentSettingsToFill The persistent properties to fill.
    * @param key The current key to convert.
    * @param value The value to convert.
    */
   protected void addPersistentPackageManagementProperty(Map<String, Object> connectionSettings, 
                                                         Properties persistentSettingsToFill, 
                                                         String key, 
                                                         DSPackageManagement value) {
      persistentSettingsToFill.setProperty(key, value.toString());
      persistentSettingsToFill.setProperty(key + TYPE_SUFFIX, TYPE_DS_PACKAGE_MANAGEMENT);
   }

   /**
    * Adds the {@link Boolean} property to the persistent properties. 
    * @param connectionSettings All connection settings.
    * @param persistentSettingsToFill The persistent properties to fill.
    * @param key The current key to convert.
    * @param value The value to convert.
    */
   protected void addPersistentBooleanProperty(Map<String, Object> connectionSettings, 
                                               Properties persistentSettingsToFill, 
                                               String key, 
                                               Boolean value) {
      persistentSettingsToFill.setProperty(key, value.toString());
      persistentSettingsToFill.setProperty(key + TYPE_SUFFIX, TYPE_BOOLEAN);
   }
   
   /**
    * Makes sure that the connection settings not contains a property with
    * the current key + type suffix.
    * @param connectionSettings All connection settings to convert.
    * @param key The current key without the type suffix to check. 
    */
   protected void checkTypeProperty(Map<String, Object> connectionSettings,
                                    String key) {
      if (connectionSettings.containsKey(key + TYPE_SUFFIX)) {
         throw new IllegalArgumentException("Can't convert entry \"" + key + "\" to persitent properties, because the map also contains key \"" + key + TYPE_SUFFIX + "\".");
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Map<String, Object> fromPersistentProperties(Properties persistentProperties) {
      Map<String, Object> result = new HashMap<String, Object>();
      Set<String> keys = persistentProperties.stringPropertyNames();
      for (String key : keys) {
         // Check if it is a value or a type property
         if (!isTypeProperty(persistentProperties, key)) {
            String type = persistentProperties.getProperty(key + TYPE_SUFFIX);
            if (TYPE_BOOLEAN.equals(type)) {
               addLoadedBooleanProperty(persistentProperties, result, key, persistentProperties.getProperty(key));
            }
            else if (TYPE_DS_PACKAGE_MANAGEMENT.equals(type)) {
               addLoadedPackageManagementProperty(persistentProperties, result, key, persistentProperties.getProperty(key));
            }
            else if (TYPE_FILE.equals(type)) {
               addLoadedFileProperty(persistentProperties, result, key, persistentProperties.getProperty(key));
            }
            else if (TYPE_PATH.equals(type)) {
               addLoadedPathProperty(persistentProperties, result, key, persistentProperties.getProperty(key));
            }
            else {
               throw new IllegalArgumentException("Unknown type \"" + type + "\" for key \"" + key + "\".");
            }
         }
      }
      return result;
   }

   /**
    * Checks if the given key is a value or a type property.
    * @param persistentProperties All properties.
    * @param key The key to check.
    * @return {@code true} = type property, {@code false} = value property
    */
   protected boolean isTypeProperty(Properties persistentProperties, String key) {
      if (key != null && key.endsWith(TYPE_SUFFIX)) {
         return persistentProperties.containsKey(key.substring(0, key.length() - TYPE_SUFFIX.length()));
      }
      else {
         return false;
      }
   }

   /**
    * Adds the loaded value from the persistent properties to the result {@link Map}.
    * @param persistentProperties All available persistent properties.
    * @param connectionSettingsToFill The result {@link Map} to fill.
    * @param key The key of the current value.
    * @param value The current value to load.
    */
   protected void addLoadedBooleanProperty(Properties persistentProperties, 
                                           Map<String, Object> connectionSettingsToFill, 
                                           String key, 
                                           String value) {
      if (value != null) {
         connectionSettingsToFill.put(key, Boolean.valueOf(value));
      }
      else {
         connectionSettingsToFill.put(key, null);
      }
   }

   /**
    * Adds the loaded value from the persistent properties to the result {@link Map}.
    * @param persistentProperties All available persistent properties.
    * @param connectionSettingsToFill The result {@link Map} to fill.
    * @param key The key of the current value.
    * @param value The current value to load.
    */
   protected void addLoadedPackageManagementProperty(Properties persistentProperties, 
                                                     Map<String, Object> connectionSettingsToFill, 
                                                     String key, 
                                                     String value) {
      if (value != null) {
         connectionSettingsToFill.put(key, DSPackageManagement.valueOf(value));
      }
      else {
         connectionSettingsToFill.put(key, null);
      }
   }

   /**
    * Adds the loaded value from the persistent properties to the result {@link Map}.
    * @param persistentProperties All available persistent properties.
    * @param connectionSettingsToFill The result {@link Map} to fill.
    * @param key The key of the current value.
    * @param value The current value to load.
    */
   protected void addLoadedFileProperty(Properties persistentProperties, 
                                        Map<String, Object> connectionSettingsToFill, 
                                        String key, 
                                        String value) {
      if (value != null) {
         connectionSettingsToFill.put(key, new File(value));
      }
      else {
         connectionSettingsToFill.put(key, null);
      }
   }

   /**
    * Adds the loaded value from the persistent properties to the result {@link Map}.
    * @param persistentProperties All available persistent properties.
    * @param connectionSettingsToFill The result {@link Map} to fill.
    * @param key The key of the current value.
    * @param value The current value to load.
    */
   protected void addLoadedPathProperty(Properties persistentProperties, 
                                        Map<String, Object> connectionSettingsToFill, 
                                        String key, 
                                        String value) {
      if (value != null) {
         connectionSettingsToFill.put(key, new Path(value));
      }
      else {
         connectionSettingsToFill.put(key, null);
      }
   }
}