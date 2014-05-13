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

package org.key_project.util.eclipse.setup;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.IStartup;
import org.key_project.util.Activator;
import org.key_project.util.eclipse.Logger;

/**
 * This class allows via extension point {@value #PREFERENCE_WORKSPACE_INITIALIZED_PREFIX}
 * registered {@link ISetupParticipant}s to initialize the workspace once
 * via {@link ISetupParticipant#setupWorkspace()} or on each startup via
 * {@link ISetupParticipant#startup()}.
 * @author Martin Hentschel
 * @see ISetupParticipant
 */
public final class SetupStartup implements IStartup {
   /**
    * The ID of the setup participants extension point.
    */
   public static final String SETUP_PARTICIPANTS_EXTENSION_POINT = "org.key_project.util.setupParticipants";
   
   /**
    * The prefix of preferences followed by {@link ISetupParticipant#getID()}
    * to store that {@link ISetupParticipant#setupWorkspace()} was executed before
    * and thus the workspace is initialized.
    */
   private static final String PREFERENCE_WORKSPACE_INITIALIZED_PREFIX = "org.key_project.util.workspaceInitialized_";
   
   /**
    * Indicates that the setup via {@link #earlyStartup()} has completed.
    */
   private static boolean setupDone = false;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void earlyStartup() {
      try {
         List<ISetupParticipant> participants = getSetupParticipants();
         for (ISetupParticipant participant : participants) {
            String id = participant.getID();
            if (!isWorkspaceInitialized(id)) {
               participant.setupWorkspace();
               setWorkspaceInitialized(id);
            }
            participant.startup();
         }
      }
      finally {
         setupDone = true;
      }
   }
   
   /**
    * Reads all available {@link ISetupParticipant} from the extension point
    * and creates the instances.
    * @return The created {@link ISetupParticipant} instances.
    */
   private static List<ISetupParticipant> getSetupParticipants() {
      // Create result list
      List<ISetupParticipant> participants = new LinkedList<ISetupParticipant>();
      Set<String> usedIDs = new HashSet<String>();
      // Add drivers registered by the extension point
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(SETUP_PARTICIPANTS_EXTENSION_POINT);
         if (point != null) {
            // Analyze the extension point
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     ISetupParticipant participant = (ISetupParticipant)configElement.createExecutableExtension("class");
                     if (usedIDs.add(participant.getID())) {
                        participants.add(participant);
                     }
                     else {
                        new Logger(Activator.getDefault(), Activator.PLUGIN_ID).logError("ISetupParticipant with id \"" + participant.getID() + "\" already found and ignored second instance.");
                     }
                  }
                  catch (Exception e) {
                     new Logger(Activator.getDefault(), Activator.PLUGIN_ID).logError(e);
                  }
               }
            }
         }
         else {
            new Logger(Activator.getDefault(), Activator.PLUGIN_ID).logError("Extension point \"" + SETUP_PARTICIPANTS_EXTENSION_POINT + "\" doesn't exist.");
         }
      }
      else {
         new Logger(Activator.getDefault(), Activator.PLUGIN_ID).logError("Extension point registry is not loaded.");
      }
      return participants;
   }
   
   /**
    * Checks if the {@link ISetupParticipant} with the given ID
    * has already initialized the workspace via {@link ISetupParticipant#setupWorkspace()}.
    * @param id The ID of the {@link ISetupParticipant}.
    * @return {@code true} workspace already initialized, {@code false} workspace not initialized yet.
    */
   public static boolean isWorkspaceInitialized(String id) {
      return getStore().getBoolean(PREFERENCE_WORKSPACE_INITIALIZED_PREFIX + id);
   }
   
   /**
    * Marks that the {@link ISetupParticipant} with the given ID has
    * already initialized the workspace via {@link ISetupParticipant#setupWorkspace()}.
    * @param id The ID of the {@link ISetupParticipant}.
    */
   private static void setWorkspaceInitialized(String id) {
      getStore().setValue(PREFERENCE_WORKSPACE_INITIALIZED_PREFIX + id, true);
   }
   
   /**
    * Returns the {@link IPreferenceStore} to use.
    * @return The {@link IPreferenceStore} to use.
    */
   private static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Checks if the setup process has completed.
    * @return {@code false} setup process not completed (may still running), {@code true} setup process completed.
    */
   public static boolean isSetupDone() {
      return setupDone;
   }
}