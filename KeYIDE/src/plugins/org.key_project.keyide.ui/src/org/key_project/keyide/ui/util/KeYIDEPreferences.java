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

package org.key_project.keyide.ui.util;

import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.RGB;
import org.key_project.keyide.ui.Activator;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

/**
 * <p>
 * Provides access to the preferences of the KeY visualization.
 * </p>
 * <p>
 * Default values are defined via {@link KeYIDEPreferencesInitializer}.
 * </p>
 * @author Marco Drebing, Niklas Bunzel, Christoph Schneider, Stefan Käsdorf
 */
public class KeYIDEPreferences {
   /**
    * Preference key for the maximal number of set nodes per branch on run.
    */
   public static final String SWITCH_TO_KEY_PERSPECTIVE = "org.key_project.keyide.ui.visualization.switchToKeyPerspective";

   /**
    * Preference key for the color of a closed {@link Goal}.
    */
   public static final String CLOSED_GOAL_COLOR = "org.key_project.keyide.ui.color.closedGoal";

   /**
    * Preference key for the color of a linked {@link Goal}.
    */
   public static final String LINKED_GOAL_COLOR = "org.key_project.keyide.ui.color.linkedGoal";

   /**
    * Preference key for the color of a disabled {@link Goal}.
    */
   public static final String DISABLED_GOAL_COLOR = "org.key_project.keyide.ui.color.disabledGoal";

   /**
    * Preference key for the color of an open {@link Goal}.
    */
   public static final String OPEN_GOAL_COLOR = "org.key_project.keyide.ui.color.openGoal";

   /**
    * Preference key for the color of a {@link Node} with notes.
    */
   public static final String NODE_WITH_NOTES_COLOR = "org.key_project.keyide.ui.color.nodeWithNotes";

   /**
    * Preference key for the color of a {@link Node} with an active statement.
    */
   public static final String NODE_WITH_ACTIVE_STATEMENT_COLOR = "org.key_project.keyide.ui.color.nodeWithActiveStatement";

   /**
    * Preference key for the color of a {@link Node} which is part of the search result.
    */
   public static final String FOUND_NODE_COLOR = "org.key_project.keyide.ui.color.foundNodeColor";

   /**
    * Returns the managed {@link IPreferenceStore}.
    * @return The managed {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Returns the property which defines the behavior when a switch to the key perspective is requested.
    * @return The property which defines the behavior when a switch to the key perspective is requested. It is one of {@link MessageDialogWithToggle#ALWAYS}, {@link MessageDialogWithToggle#PROMPT} or {@link MessageDialogWithToggle#NEVER}.
    */
   public static String getSwitchToKeyPerspective() {
      return getStore().getString(SWITCH_TO_KEY_PERSPECTIVE);
   }
   
   /**
    * Returns the default property which defines the behavior when a switch to the key perspective is requested.
    * @return The default property which defines the behavior when a switch to the key perspective is requested. It is one of {@link MessageDialogWithToggle#ALWAYS}, {@link MessageDialogWithToggle#PROMPT} or {@link MessageDialogWithToggle#NEVER}.
    */
   public static String getDefaultSwitchToKeyPerspective() {
      return getStore().getDefaultString(SWITCH_TO_KEY_PERSPECTIVE);
   }
   
   /**
    * Sets the property which defines the behavior when a switch to the key perspective is requested.
    * @param value The property which defines the behavior when a switch to the key perspective is requested. It must be {@link MessageDialogWithToggle#ALWAYS}, {@link MessageDialogWithToggle#PROMPT} or {@link MessageDialogWithToggle#NEVER}.
    */
   public static void setSwitchToKeyPerspective(String value) {
      getStore().setValue(SWITCH_TO_KEY_PERSPECTIVE, value);
   }
   
   /**
    * Sets the property which defines the behavior when a switch to the state key perspective is requested.
    * @param defaultValue The default property which defines the behavior when a switch to the key perspective is requested. It must be {@link MessageDialogWithToggle#ALWAYS}, {@link MessageDialogWithToggle#PROMPT} or {@link MessageDialogWithToggle#NEVER}.
    */
   public static void setDefaultSwitchToKeyPerspective(String defaultValue) {
      getStore().setDefault(SWITCH_TO_KEY_PERSPECTIVE, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getClosedGoalColor() {
      return PreferenceConverter.getColor(getStore(), CLOSED_GOAL_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultClosedGoalColor() {
      return PreferenceConverter.getDefaultColor(getStore(), CLOSED_GOAL_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setClosedGoalColor(RGB value) {
      PreferenceConverter.setValue(getStore(), CLOSED_GOAL_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultClosedGoalColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), CLOSED_GOAL_COLOR, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getLinkedGoalColor() {
      return PreferenceConverter.getColor(getStore(), LINKED_GOAL_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultLinkedGoalColor() {
      return PreferenceConverter.getDefaultColor(getStore(), LINKED_GOAL_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setLinkedGoalColor(RGB value) {
      PreferenceConverter.setValue(getStore(), LINKED_GOAL_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultLinkedGoalColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), LINKED_GOAL_COLOR, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getDisabledGoalColor() {
      return PreferenceConverter.getColor(getStore(), DISABLED_GOAL_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultDisabledGoalColor() {
      return PreferenceConverter.getDefaultColor(getStore(), DISABLED_GOAL_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setDisabledGoalColor(RGB value) {
      PreferenceConverter.setValue(getStore(), DISABLED_GOAL_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultDisabledGoalColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), DISABLED_GOAL_COLOR, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getOpenGoalColor() {
      return PreferenceConverter.getColor(getStore(), OPEN_GOAL_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultOpenGoalColor() {
      return PreferenceConverter.getDefaultColor(getStore(), OPEN_GOAL_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setOpenGoalColor(RGB value) {
      PreferenceConverter.setValue(getStore(), OPEN_GOAL_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultOpenGoalColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), OPEN_GOAL_COLOR, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getNodeWithNotesColor() {
      return PreferenceConverter.getColor(getStore(), NODE_WITH_NOTES_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultNodeWithNotesColor() {
      return PreferenceConverter.getDefaultColor(getStore(), NODE_WITH_NOTES_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setNodeWithNotesColor(RGB value) {
      PreferenceConverter.setValue(getStore(), NODE_WITH_NOTES_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultNodeWithNotesColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), NODE_WITH_NOTES_COLOR, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getNodeWithActiveStatementColor() {
      return PreferenceConverter.getColor(getStore(), NODE_WITH_ACTIVE_STATEMENT_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultNodeWithActiveStatementColor() {
      return PreferenceConverter.getDefaultColor(getStore(), NODE_WITH_ACTIVE_STATEMENT_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setNodeWithActiveStatementColor(RGB value) {
      PreferenceConverter.setValue(getStore(), NODE_WITH_ACTIVE_STATEMENT_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultNodeWithActiveStatementColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), NODE_WITH_ACTIVE_STATEMENT_COLOR, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getFoundNodeColor() {
      return PreferenceConverter.getColor(getStore(), FOUND_NODE_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultFoundNodeColor() {
      return PreferenceConverter.getDefaultColor(getStore(), FOUND_NODE_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setFoundNodeColor(RGB value) {
      PreferenceConverter.setValue(getStore(), FOUND_NODE_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultFoundNodeColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), FOUND_NODE_COLOR, defaultValue);
   }
}