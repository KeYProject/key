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

package org.key_project.sed.ui.visualization.util;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.Activator;

/**
 * <p>
 * Provides access to the preferences of the Symbolic Execution Debugger visualization.
 * </p>
 * <p>
 * Default values are defined via {@link VisualizationPreferencesInitializer}.
 * </p>
 * @author Martin Hentschel
 * @see KeYSEDPreferencesInitializer.
 */
public class VisualizationPreferences {
   /**
    * Preference key for the maximal number of set nodes per branch on run.
    */
   public static final String SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE = "org.key_project.sed.ui.visualization.preference.switchToStateVisualizationPerspective";

   /**
    * Preference key for the first background color of {@link ISEDDebugNode}s.
    */
   public static final String EXECUTION_TREE_NODE_FIRST_BACKGROUND_COLOR = "org.key_project.sed.ui.visualization.preference.executionTreeNodeFirstBackgroundColor";

   /**
    * Preference key for the second background color of {@link ISEDDebugNode}s.
    */
   public static final String EXECUTION_TREE_NODE_SECOND_BACKGROUND_COLOR = "org.key_project.sed.ui.visualization.preference.executionTreeNodeSecondBackgroundColor";

   /**
    * Preference key for the direction of background colors in {@link ISEDDebugNode}s.
    */
   public static final String EXECUTION_TREE_NODE_BACKGROUND_DIRECTION = "org.key_project.sed.ui.visualization.preference.executionTreeNodeBackgroundDirection";

   /**
    * Horizontal preference value of {@link #EXECUTION_TREE_NODE_BACKGROUND_DIRECTION}.
    */
   public static final String EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_HORIZONTAL = "horizontal";

   /**
    * Vertical preference value of {@link #EXECUTION_TREE_NODE_BACKGROUND_DIRECTION}.
    */
   public static final String EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_VERTICAL = "vertical";

   /**
    * Preference key for the foreground color of {@link ISEDDebugNode}s.
    */
   public static final String EXECUTION_TREE_NODE_FOREGROUND_COLOR = "org.key_project.sed.ui.visualization.preference.executionTreeNodeForegroundColor";

   /**
    * Preference key for the text color of {@link ISEDDebugNode}s.
    */
   public static final String EXECUTION_TREE_NODE_TEXT_COLOR = "org.key_project.sed.ui.visualization.preference.executionTreeNodeTextColor";

   /**
    * Preference key for the connection color between {@link ISEDDebugNode}s.
    */
   public static final String EXECUTION_TREE_NODE_CONNECTION_COLOR = "org.key_project.sed.ui.visualization.preference.executionTreeNodeConnectionColor";

   /**
    * Returns the managed {@link IPreferenceStore}.
    * @return The managed {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Returns the property which defines the behavior when a switch to the state visualization perspective is requested.
    * @return The property which defines the behavior when a switch to the state visualization perspective is requested.
    */
   public static String getSwitchToStateVisualizationPerspective() {
      return getStore().getString(SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE);
   }
   
   /**
    * Returns the default property which defines the behavior when a switch to the state visualization perspective is requested.
    * @return The default property which defines the behavior when a switch to the state visualization perspective is requested.
    */
   public static String getDefaultSwitchToStateVisualizationPerspective() {
      return getStore().getDefaultString(SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE);
   }
   
   /**
    * Sets the property which defines the behavior when a switch to the state visualization perspective is requested.
    * @param value The property which defines the behavior when a switch to the state visualization perspective is requested.
    */
   public static void setSwitchToStateVisualizationPerspective(String value) {
      getStore().setValue(SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE, value);
   }
   
   /**
    * Sets the property which defines the behavior when a switch to the state visualization perspective is requested.
    * @param defaultValue The default property which defines the behavior when a switch to the state visualization perspective is requested.
    */
   public static void setDefaultSwitchToStateVisualizationPerspective(String defaultValue) {
      getStore().setDefault(SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getExecutionTreeNodeFirstBackgroundColor() {
      return PreferenceConverter.getColor(getStore(), EXECUTION_TREE_NODE_FIRST_BACKGROUND_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultExecutionTreeNodeFirstBackgroundColor() {
      return PreferenceConverter.getDefaultColor(getStore(), EXECUTION_TREE_NODE_FIRST_BACKGROUND_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setExecutionTreeNodeFirstBackgroundColor(RGB value) {
      PreferenceConverter.setValue(getStore(), EXECUTION_TREE_NODE_FIRST_BACKGROUND_COLOR, value);
   }
   
   /**
    * Sets the default value.
    * @param defaultValue The new default value to set.
    */
   public static void setDefaultExecutionTreeNodeFirstBackgroundColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), EXECUTION_TREE_NODE_FIRST_BACKGROUND_COLOR, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getExecutionTreeNodeSecondBackgroundColor() {
      return PreferenceConverter.getColor(getStore(), EXECUTION_TREE_NODE_SECOND_BACKGROUND_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultExecutionTreeNodeSecondBackgroundColor() {
      return PreferenceConverter.getDefaultColor(getStore(), EXECUTION_TREE_NODE_SECOND_BACKGROUND_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setExecutionTreeNodeSecondBackgroundColor(RGB value) {
      PreferenceConverter.setValue(getStore(), EXECUTION_TREE_NODE_SECOND_BACKGROUND_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultExecutionTreeNodeSecondBackgroundColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), EXECUTION_TREE_NODE_SECOND_BACKGROUND_COLOR, defaultValue);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static boolean isExecutionTreeNodeDirectionHorizontal() {
      return EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_HORIZONTAL.equals(getStore().getString(EXECUTION_TREE_NODE_BACKGROUND_DIRECTION));
   }
   
   /**
    * Returns the default property which defines the behavior when a switch to the state visualization perspective is requested.
    * @return The default property which defines the behavior when a switch to the state visualization perspective is requested.
    */
   public static boolean isDefaultExecutionTreeNodeDirectionHorizontal() {
      return EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_HORIZONTAL.equals(getStore().getDefaultString(EXECUTION_TREE_NODE_BACKGROUND_DIRECTION));
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setExecutionTreeNodeDirectionHorizontal(boolean value) {
      getStore().setValue(EXECUTION_TREE_NODE_BACKGROUND_DIRECTION, value ? EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_HORIZONTAL : EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_VERTICAL);
   }
   
   /**
    * Sets the default value.
    * @param defaultValue The new default value to set.
    */
   public static void setDefaultExecutionTreeNodeDirectionHorizontal(boolean defaultValue) {
      getStore().setDefault(EXECUTION_TREE_NODE_BACKGROUND_DIRECTION, defaultValue ? EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_HORIZONTAL : EXECUTION_TREE_NODE_BACKGROUND_DIRECTION_VERTICAL);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getExecutionTreeNodeForegroundColor() {
      return PreferenceConverter.getColor(getStore(), EXECUTION_TREE_NODE_FOREGROUND_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultExecutionTreeNodeForegroundColor() {
      return PreferenceConverter.getDefaultColor(getStore(), EXECUTION_TREE_NODE_FOREGROUND_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setExecutionTreeNodeForegroundColor(RGB value) {
      PreferenceConverter.setValue(getStore(), EXECUTION_TREE_NODE_FOREGROUND_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultExecutionTreeNodeForegroundColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), EXECUTION_TREE_NODE_FOREGROUND_COLOR, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getExecutionTreeNodeTextColor() {
      return PreferenceConverter.getColor(getStore(), EXECUTION_TREE_NODE_TEXT_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultExecutionTreeNodeTextColor() {
      return PreferenceConverter.getDefaultColor(getStore(), EXECUTION_TREE_NODE_TEXT_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setExecutionTreeNodeTextColor(RGB value) {
      PreferenceConverter.setValue(getStore(), EXECUTION_TREE_NODE_TEXT_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultExecutionTreeNodeTextColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), EXECUTION_TREE_NODE_TEXT_COLOR, defaultValue);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static RGB getExecutionTreeNodeConnectionColor() {
      return PreferenceConverter.getColor(getStore(), EXECUTION_TREE_NODE_CONNECTION_COLOR);
   }
   
   /**
    * Returns the default value.
    * @return The default value.
    */
   public static RGB getDefaultExecutionTreeNodeConnectionColor() {
      return PreferenceConverter.getDefaultColor(getStore(), EXECUTION_TREE_NODE_CONNECTION_COLOR);
   }
   
   /**
    * Sets the current value.
    * @param value The new value to set.
    */
   public static void setExecutionTreeNodeConnectionColor(RGB value) {
      PreferenceConverter.setValue(getStore(), EXECUTION_TREE_NODE_CONNECTION_COLOR, value);
   }
   
   /**
    * Returns the current value.
    * @return The current value.
    */
   public static void setDefaultExecutionTreeNodeConnectionColor(RGB defaultValue) {
      PreferenceConverter.setDefault(getStore(), EXECUTION_TREE_NODE_CONNECTION_COLOR, defaultValue);
   }
}