package org.key_project.key4eclipse.common.ui.util;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.common.ui.wizard.StarterWizard;
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
    * Contains all available {@link StarterDescription}s of {@link IGlobalStarter}s.
    */
   private static ImmutableList<StarterDescription<IGlobalStarter>> globalStarters;
   
   /**
    * Contains all available {@link StarterDescription}s of {@link IMethodStarter}s.
    */
   private static ImmutableList<StarterDescription<IMethodStarter>> methodStarters;

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
}
