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

package org.key_project.key4eclipse.common.ui.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.common.ui.expression.FileStarterAvailablePropertyTester;
import org.key_project.key4eclipse.common.ui.expression.GlobalStarterAvailablePropertyTester;
import org.key_project.key4eclipse.common.ui.expression.MethodStarterAvailablePropertyTester;
import org.key_project.key4eclipse.common.ui.expression.ProjectStarterAvailablePropertyTester;
import org.key_project.key4eclipse.common.ui.starter.IFileStarter;
import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.common.ui.starter.IProjectStarter;
import org.key_project.key4eclipse.common.ui.wizard.StarterWizard;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;

/**
 * Provides utility method to work with starts registered via extension points.
 * @author Martin Hentschel
 */
public final class StarterUtil {
   /**
    * ID of the used extension point.
    */
   public static final String GLOBAL_STARTER_EXTENSION_POINT = "org.key_project.key4eclipse.common.ui.globalStarter";
   
   /**
    * ID of the used extension point.
    */
   public static final String METHOD_STARTER_EXTENSION_POINT = "org.key_project.key4eclipse.common.ui.methodStarter";
   
   /**
    * ID of the used extension point.
    */
   public static final String FILE_STARTER_EXTENSION_POINT = "org.key_project.key4eclipse.common.ui.fileStarter";
   
   /**
    * ID of the used extension point.
    */
   public static final String PROJECT_STARTER_EXTENSION_POINT = "org.key_project.key4eclipse.common.ui.projectStarter";
   
   /**
    * Contains all available {@link StarterDescription}s of {@link IGlobalStarter}s.
    */
   private static ImmutableList<StarterDescription<IGlobalStarter>> globalStarters;
   
   /**
    * Contains all available {@link StarterDescription}s of {@link IMethodStarter}s.
    */
   private static ImmutableList<StarterDescription<IMethodStarter>> methodStarters;
   
   /**
    * Contains all available {@link StarterDescription}s of {@link IFileStarter}s.
    */
   private static ImmutableList<StarterDescription<IFileStarter>> fileStarters;
   
   /**
    * Contains all available {@link StarterDescription}s of {@link IProjectStarter}s.
    */
   private static ImmutableList<StarterDescription<IProjectStarter>> projectStarters;

   /**
    * Forbid instances.
    */
   private StarterUtil() {
   }
   
   /**
    * Returns all available {@link StarterDescription}s of {@link IGlobalStarter}s.
    * @return The available {@link StarterDescription}s of  {@link IGlobalStarter}s.
    */
   public static ImmutableList<StarterDescription<IGlobalStarter>> getGlobalStarters() {
      // Lazy loading if needed
      if (globalStarters == null) {
         globalStarters = createStarters(GLOBAL_STARTER_EXTENSION_POINT, IGlobalStarter.class);
      }
      return globalStarters;
   }
   
   /**
    * Returns all available {@link StarterDescription}s of {@link IMethodStarter}s.
    * @return The available {@link StarterDescription}s of  {@link IMethodStarter}s.
    */
   public static ImmutableList<StarterDescription<IMethodStarter>> getMethodStarters() {
      // Lazy loading if needed
      if (methodStarters == null) {
         methodStarters = createStarters(METHOD_STARTER_EXTENSION_POINT, IMethodStarter.class);
      }
      return methodStarters;
   }
   
   /**
    * Returns all available {@link StarterDescription}s of {@link IFileStarter}s.
    * @return The available {@link StarterDescription}s of  {@link IFileStarter}s.
    */
   public static ImmutableList<StarterDescription<IFileStarter>> getFileStarters() {
      // Lazy loading if needed
      if (fileStarters == null) {
         fileStarters = createStarters(FILE_STARTER_EXTENSION_POINT, IFileStarter.class);
      }
      return fileStarters;
   }
   
   /**
    * Returns all available {@link StarterDescription}s of {@link IProjectStarter}s.
    * @return The available {@link StarterDescription}s of  {@link IProjectStarter}s.
    */
   public static ImmutableList<StarterDescription<IProjectStarter>> getProjectStarters() {
      // Lazy loading if needed
      if (projectStarters == null) {
         projectStarters = createStarters(PROJECT_STARTER_EXTENSION_POINT, IProjectStarter.class);
      }
      return projectStarters;
   }
   
   /**
    * Reads all available {@link StarterDescription}s from the extension point.
    * @param extensionPoint The extension point to read from.
    * @param expectedClass The expected {@link Class} of the registered instances.
    * @return The created {@link StarterDescription}s instances.
    */
   private static <I> ImmutableList<StarterDescription<I>> createStarters(String extensionPoint, 
                                                                          Class<I> expectedClass) {
      // Create result list
      ImmutableList<StarterDescription<I>> result = ImmutableSLList.nil();
      // Add drivers registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(extensionPoint);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     String id = configElement.getAttribute("id");
                     if (StringUtil.isEmpty(id)) {
                        throw new IllegalStateException("ID of starter is not defined.");
                     }
                     if (searchGlobalStarter(result, id) != null) {
                        throw new IllegalStateException("Starter ID \"" + id + "\" is used multiple times.");
                     }
                     String name = configElement.getAttribute("name");
                     if (StringUtil.isEmpty(name)) {
                        throw new IllegalStateException("Name of starter with ID \"" + id + "\" is not defined.");
                     }
                     Object instance = configElement.createExecutableExtension("class");
                     if (!(expectedClass.isInstance(instance))) {
                        throw new IllegalStateException("Unsupported class of starter with ID \"" + id + "\" found.");
                     }
                     String description = configElement.getAttribute("description");
                     
                     result = result.append(new StarterDescription<I>(id, name, expectedClass.cast(instance), description));
                  }
                  catch (Exception e) {
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
         else {
            LogUtil.getLogger().logError("Extension point \"" + extensionPoint + "\" doesn't exist.");
         }
      }
      else {
         LogUtil.getLogger().logError("Extension point registry is not loaded.");
      }
      return result;
   }
   
   /**
    * Searches the {@link StarterDescription} with the given ID.
    * @param starters The {@link StarterDescription} to search in.
    * @param id The ID to search.
    * @return The found {@link StarterDescription} or {@code null} if not available.
    */
   public static <I> StarterDescription<I> searchGlobalStarter(ImmutableList<StarterDescription<I>> starters, 
                                                               final String id) {
      return CollectionUtil.search(starters, new IFilter<StarterDescription<I>>() {
         @Override
         public boolean select(StarterDescription<I> element) {
            return ObjectUtil.equals(id, element.getId());
         }
      });
   }
   
   /**
    * Checks if global starter are available or not.
    * @return {@code true} available, {@code false} not available.
    */
   public static boolean areGlobalStartersAvailable() {
      ImmutableList<StarterDescription<IGlobalStarter>> starter = getGlobalStarters();
      return !starter.isEmpty() && !StarterPreferenceUtil.isGlobalStarterDisabled();
   }
   
   /**
    * Opens the global starter.
    * @param parentShell The parent {@link Shell} to use.
    * @throws Exception Occurred Exception.
    */
   public static void openGlobalStarter(Shell parentShell) throws Exception {
      ImmutableList<StarterDescription<IGlobalStarter>> starterDescriptions = getGlobalStarters();
      StarterDescription<IGlobalStarter> starter = StarterWizard.openWizard(parentShell, 
                                                                            "Open Application", 
                                                                            "Select application", 
                                                                            "Select the application to open.", 
                                                                            starterDescriptions, 
                                                                            StarterPreferenceUtil.SELECTED_GLOBAL_STARTER_ID, 
                                                                            StarterPreferenceUtil.DONT_ASK_FOR_GLOBAL_STARTER, 
                                                                            StarterPreferenceUtil.GLOBAL_STARTER_DISABLED);
      if (starter != null && starter.getInstance() != null) {
         starter.getInstance().open();
      }
   }
   
   /**
    * Checks if method starter are available or not.
    * @return {@code true} available, {@code false} not available.
    */
   public static boolean areMethodStartersAvailable() {
      ImmutableList<StarterDescription<IMethodStarter>> starter = getMethodStarters();
      return !starter.isEmpty() && !StarterPreferenceUtil.isMethodStarterDisabled();
   }
   
   /**
    * Opens the method starter.
    * @param parentShell The parent {@link Shell} to use.
    * @param method The {@link IMethod} to load.
    * @throws Exception Occurred Exception.
    */
   public static void openMethodStarter(Shell parentShell, IMethod method) throws Exception {
      ImmutableList<StarterDescription<IMethodStarter>> starterDescriptions = getMethodStarters();
      StarterDescription<IMethodStarter> starter = StarterWizard.openWizard(parentShell, 
                                                                            "Start Proof", 
                                                                            "Select application", 
                                                                            "Select the application to start proof in.", 
                                                                            starterDescriptions, 
                                                                            StarterPreferenceUtil.SELECTED_METHOD_STARTER_ID, 
                                                                            StarterPreferenceUtil.DONT_ASK_FOR_METHOD_STARTER, 
                                                                            StarterPreferenceUtil.METHOD_STARTER_DISABLED);
      if (starter != null && starter.getInstance() != null) {
         starter.getInstance().open(method);
      }
   }
   
   /**
    * Checks if file starter are available or not.
    * @return {@code true} available, {@code false} not available.
    */
   public static boolean areFileStartersAvailable() {
      ImmutableList<StarterDescription<IFileStarter>> starter = getFileStarters();
      return !starter.isEmpty() && !StarterPreferenceUtil.isFileStarterDisabled();
   }
   
   /**
    * Opens the file starter.
    * @param parentShell The parent {@link Shell} to use.
    * @param file The {@link IFile} to load.
    * @throws Exception Occurred Exception.
    */
   public static void openFileStarter(Shell parentShell, IFile file) throws Exception {
      ImmutableList<StarterDescription<IFileStarter>> starterDescriptions = getFileStarters();
      StarterDescription<IFileStarter> starter = StarterWizard.openWizard(parentShell, 
                                                                          "Load File", 
                                                                          "Select application", 
                                                                          "Select the application to load file in.", 
                                                                          starterDescriptions, 
                                                                          StarterPreferenceUtil.SELECTED_FILE_STARTER_ID, 
                                                                          StarterPreferenceUtil.DONT_ASK_FOR_FILE_STARTER, 
                                                                          StarterPreferenceUtil.FILE_STARTER_DISABLED);
      if (starter != null && starter.getInstance() != null) {
         starter.getInstance().open(file);
      }
   }
   
   /**
    * Checks if project starter are available or not.
    * @return {@code true} available, {@code false} not available.
    */
   public static boolean areProjectStartersAvailable() {
      ImmutableList<StarterDescription<IProjectStarter>> starter = getProjectStarters();
      return !starter.isEmpty() && !StarterPreferenceUtil.isProjectStarterDisabled();
   }
   
   /**
    * Opens the project starter.
    * @param parentShell The parent {@link Shell} to use.
    * @param project The {@link IProject} to load.
    * @throws Exception Occurred Exception.
    */
   public static void openProjectStarter(Shell parentShell, IProject project) throws Exception {
      ImmutableList<StarterDescription<IProjectStarter>> starterDescriptions = getProjectStarters();
      StarterDescription<IProjectStarter> starter = StarterWizard.openWizard(parentShell, 
                                                                             "Load Project", 
                                                                             "Select application", 
                                                                             "Select the application to load project in.", 
                                                                             starterDescriptions, 
                                                                             StarterPreferenceUtil.SELECTED_PROJECT_STARTER_ID, 
                                                                             StarterPreferenceUtil.DONT_ASK_FOR_PROJECT_STARTER, 
                                                                             StarterPreferenceUtil.PROJECT_STARTER_DISABLED);
      if (starter != null && starter.getInstance() != null) {
         starter.getInstance().open(project);
      }
   }

   /**
    * Re-evaluates all properties defined by {@link GlobalStarterAvailablePropertyTester},
    * {@link MethodStarterAvailablePropertyTester}, {@link FileStarterAvailablePropertyTester}
    * and {@link ProjectStarterAvailablePropertyTester}.
    */
   public static void updatePropertyTester() {
      WorkbenchUtil.updatePropertyTesters("org.key_project.key4eclipse.common.ui.globalStarterAvailable",
                                          "org.key_project.key4eclipse.common.ui.methodStarterAvailable",
                                          "org.key_project.key4eclipse.common.ui.fileStarterAvailable",
                                          "org.key_project.key4eclipse.common.ui.projectStarterAvailable");
   }
}