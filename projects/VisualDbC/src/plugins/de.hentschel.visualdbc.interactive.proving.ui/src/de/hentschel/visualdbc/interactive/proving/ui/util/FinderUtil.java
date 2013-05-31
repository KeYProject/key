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

package de.hentschel.visualdbc.interactive.proving.ui.util;

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

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinderFactory;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinderFactory;

/**
 * Provides static methods to work with {@link IDSFinderFactory}s.
 * @author Martin Hentschel
 */
public class FinderUtil {
   /**
    * ID of the used extension point.
    */
   public static final String DS_FINDER_EXTENSION_POINT = "de.hentschel.visualdbc.interactive.proving.ui.dsFinder";

   /**
    * ID of the used extension point.
    */
   public static final String DBC_FINDER_EXTENSION_POINT = "de.hentschel.visualdbc.interactive.proving.ui.dbcFinder";
   
   /**
    * Contains all available {@link IDSFinderFactory}s.
    */
   private static List<IDSFinderFactory> dsFinderFactories;
   
   /**
    * Contains all available {@link IDbcFinderFactory}s.
    */
   private static List<IDbcFinderFactory> dbcFinderFactories;
   
   /**
    * Forbid instances.
    */
   private FinderUtil() {
   }
   
   /**
    * Returns an {@link IDbcFinder} that can handle the given {@link IDSConnection}.
    * @param connection The {@link IDSConnection} to handle.
    * @param model The {@link DbcModel} to search in.
    * @return The created {@link IDbcFinder} or {@code null} if no registered {@link IDbcFinderFactory} can handle the {@link IDSConnection}.
    */
   public static IDbcFinder getDbcFinder(IDSConnection connection, DbcModel model) {
      IDbcFinderFactory factory = getDbcFinderFactory(connection);
      return factory != null ? factory.createFinder(model) : null;
   }
   
   /**
    * Returns the {@link IDbcFinderFactory} that can handle the given {@link IDSConnection}.
    * @param connection The {@link IDSConnection} to handle.
    * @return The found {@link IDbcFinderFactory} or {@code null} if no registered {@link IDbcFinderFactory} can handle the {@link IDSConnection}.
    */
   public static IDbcFinderFactory getDbcFinderFactory(IDSConnection connection) {
      IDbcFinderFactory result = null;
      Iterator<IDbcFinderFactory> iter = getDbcFinderFactories().iterator();
      while (iter.hasNext()) {
         IDbcFinderFactory next = iter.next();
         Assert.isNotNull(next);
         if (next.canHandle(connection)) {
            result = next;
         }
      }
      return result;
   }
   
   /**
    * Reads all available {@link IDbcFinderFactory} from the extension point
    * and creates the instances.
    * @return The created {@link IDbcFinderFactory} instances.
    */
   private static List<IDbcFinderFactory> createDbcFinderFactories() {
      // Create result list
      List<IDbcFinderFactory> factories = new LinkedList<IDbcFinderFactory>();
      // Add factories registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(DBC_FINDER_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     IDbcFinderFactory factory = (IDbcFinderFactory)configElement.createExecutableExtension("class");
                     factories.add(factory);
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + DBC_FINDER_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      // Sort factories by priority
      Collections.sort(factories, new Comparator<IDbcFinderFactory>() {
         @Override
         public int compare(IDbcFinderFactory o1, IDbcFinderFactory o2) {
            return o1.getPriority() - o2.getPriority();
         }
      });
      return factories;
   }
   
   /**
    * Returns all available {@link IDbcFinderFactory}s.
    * @return The available {@link IDbcFinderFactory}s.
    */
   public static List<IDbcFinderFactory> getDbcFinderFactories() {
      // Lazy loading if needed
      if (dbcFinderFactories == null) {
         dbcFinderFactories = createDbcFinderFactories();
      }
      return dbcFinderFactories;
   }
   
   /**
    * Returns an {@link IDSFinder} that can handle the given {@link IDSConnection}.
    * @param connection The {@link IDSConnection} to handle.
    * @return The created {@link IDSFinder} or {@code null} if no registered {@link IDSFinderFactory} can handle the {@link IDSConnection}.
    */
   public static IDSFinder getDSFinder(IDSConnection connection) {
      IDSFinderFactory factory = getDSFinderFactory(connection);
      return factory != null ? factory.createFinder(connection) : null;
   }
   
   /**
    * Returns the {@link IDSFinderFactory} that can handle the given {@link IDSConnection}.
    * @param connection The {@link IDSConnection} to handle.
    * @return The found {@link IDSFinderFactory} or {@code null} if no registered {@link IDSFinderFactory} can handle the {@link IDSConnection}.
    */
   public static IDSFinderFactory getDSFinderFactory(IDSConnection connection) {
      IDSFinderFactory result = null;
      Iterator<IDSFinderFactory> iter = getDSFinderFactories().iterator();
      while (iter.hasNext()) {
         IDSFinderFactory next = iter.next();
         Assert.isNotNull(next);
         if (next.canHandle(connection)) {
            result = next;
         }
      }
      return result;
   }
   
   /**
    * Reads all available {@link IDSFinderFactory} from the extension point
    * and creates the instances.
    * @return The created {@link IDSFinderFactory} instances.
    */
   private static List<IDSFinderFactory> createDSFinderFactories() {
      // Create result list
      List<IDSFinderFactory> factories = new LinkedList<IDSFinderFactory>();
      // Add factories registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(DS_FINDER_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     IDSFinderFactory factory = (IDSFinderFactory)configElement.createExecutableExtension("class");
                     factories.add(factory);
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + DS_FINDER_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      // Sort factories by priority
      Collections.sort(factories, new Comparator<IDSFinderFactory>() {
         @Override
         public int compare(IDSFinderFactory o1, IDSFinderFactory o2) {
            return o1.getPriority() - o2.getPriority();
         }
      });
      return factories;
   }
   
   /**
    * Returns all available {@link IDSFinderFactory}s.
    * @return The available {@link IDSFinderFactory}s.
    */
   public static List<IDSFinderFactory> getDSFinderFactories() {
      // Lazy loading if needed
      if (dsFinderFactories == null) {
         dsFinderFactories = createDSFinderFactories();
      }
      return dsFinderFactories;
   }
}