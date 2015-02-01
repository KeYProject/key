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

package de.hentschel.visualdbc.datasource.util;

import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.key_project.util.java.StringUtil;

import de.hentschel.visualdbc.datasource.model.IDSDriver;

/**
 * Provides static methods to work with data sources.
 * @author Martin Hentschel
 */
public final class DriverUtil {
   /**
    * ID of the used extension point.
    */
   public static final String DATA_SOURCE_EXTENSION_POINT = "de.hentschel.visualdbc.dataSource.dataSources";
   
   /**
    * Contains all available {@link IDSDriver}s.
    */
   private static List<IDSDriver> drivers;
   
   /**
    * Forbid instances.
    */
   private DriverUtil() {
   }
   
   /**
    * Returns the {@link IDSDriver} with the given ID.
    * @param id The ID.
    * @return A created {@link IDSDriver} or {@code null} if no driver with the ID is registered.
    */
   public static IDSDriver getDriver(String id) {
      IDSDriver result = null;
      Iterator<IDSDriver> iter = getDrivers().iterator();
      while (iter.hasNext()) {
         IDSDriver next = iter.next();
         Assert.isNotNull(next);
         Assert.isNotNull(next.getId());
         if (next.getId().equals(id)) {
            result = next;
         }
      }
      return result;
   }
   
   /**
    * Reads all available {@link IDSDriver} from the extension point
    * and creates the driver instances.
    * @return The created {@link IDSDriver} instances.
    */
   private static List<IDSDriver> createDrivers() {
      // Create result list
      List<IDSDriver> drivers = new LinkedList<IDSDriver>();
      // Add drivers registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(DATA_SOURCE_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     IDSDriver driver = (IDSDriver)configElement.createExecutableExtension("class");
                     if (driver != null && !StringUtil.isTrimmedEmpty(driver.getId())) {
                        drivers.add(driver);
                     }
                     else {
                        LogUtil.getLogger().logWarning("Driver registered with empty ID.");
                     }
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + DATA_SOURCE_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      // Sort drivers by priority and name
      Collections.sort(drivers, new Comparator<IDSDriver>() {
         @Override
         public int compare(IDSDriver o1, IDSDriver o2) {
            if (o1.getPriority() == o2.getPriority()) {
               return o1.getName().compareTo(o2.getName());
            }
            else {
               if (o1.getPriority() < 0) {
                  if (o2.getPriority() >= 0) {
                     return 1;
                  }
                  else {
                     return (o1.getPriority() * -1) - (o2.getPriority() * -1);
                  }
               }
               else {
                  if (o2.getPriority() >= 0) {
                     return (o2.getPriority() - o1.getPriority());
                  }
                  else {
                     return -1;
                  }
               }
            }
         }
      });
      return drivers;
   }
   
   /**
    * Returns all available {@link IDSDriver}s.
    * @return The available {@link IDSDriver}s.
    */
   public static List<IDSDriver> getDrivers() {
      // Lazy loading if needed
      if (drivers == null) {
         drivers = createDrivers();
      }
      return drivers;
   }
}