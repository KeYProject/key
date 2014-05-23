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

package org.key_project.sed.core.util;

import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.key_project.sed.core.Activator;
import org.key_project.sed.core.annotation.ISEDAnnotationType;

/**
 * Provides utility methods to edit the SED preferences.
 * @author Martin Hentschel
 */
public final class SEDPreferenceUtil {
   /**
    * Property that indicates to show the compact or normal symbolic execution tree.
    */
   public static final String PROP_SHOW_COMPACT_EXECUTION_TREE = "org.key_project.sed.preference.showCompactExecutionTree";

   /**
    * Prefix to store {@link ISEDAnnotationType#isHighlightBackground()}.
    */
   public static final String PROP_ANNOTATION_TYPE_HIGHLIGHT_BACKGROUND_PREFIX = "org.key_project.sed.preference.annotationType.highlightBackground_";

   /**
    * Prefix to store {@link ISEDAnnotationType#getBackgroundColor()}.
    */
   public static final String PROP_ANNOTATION_TYPE_BACKGROUND_COLOR_PREFIX = "org.key_project.sed.preference.annotationType.backgroundColor_";

   /**
    * Prefix to store {@link ISEDAnnotationType#isHighlightForeground()}.
    */   
   public static final String PROP_ANNOTATION_TYPE_HIGHLIGHT_FOREGROUND_PREFIX = "org.key_project.sed.preference.annotationType.highlightForeground_";

   /**
    * Prefix to store {@link ISEDAnnotationType#getForegroundColor()}.
    */
   public static final String PROP_ANNOTATION_TYPE_FOREGROUND_COLOR_PREFIX = "org.key_project.sed.preference.annotationType.foregroundColor_";
   
   /**
    * Forbid instances.
    */
   private SEDPreferenceUtil() {
   }
   
   /**
    * Returns the {@link IPreferenceStore} to edit.
    * @return The used {@link IPreferenceStore}.
    */
   public static IPreferenceStore getStore() {
      return Activator.getDefault().getPreferenceStore();
   }
   
   /**
    * Returns the current value of property {@link #PROP_SHOW_COMPACT_EXECUTION_TREE}.
    * @return The current value of property{@link #PROP_SHOW_COMPACT_EXECUTION_TREE}.
    */
   public static boolean isShowCompactExecutionTree() {
      return getStore().getBoolean(PROP_SHOW_COMPACT_EXECUTION_TREE);
   }
   
   /**
    * Returns the default value of property {@link #PROP_SHOW_COMPACT_EXECUTION_TREE}.
    * @return The default value of property{@link #PROP_SHOW_COMPACT_EXECUTION_TREE}.
    */
   public static boolean isDefaultShowCompactExecutionTree() {
      return getStore().getDefaultBoolean(PROP_SHOW_COMPACT_EXECUTION_TREE);
   }
   
   /**
    * Sets the current value of property {@link #PROP_SHOW_COMPACT_EXECUTION_TREE}.
    * @param showCompactExecutionTree The new value to set.
    */
   public static void setShowCompactExecutionTree(boolean showCompactExecutionTree) {
      getStore().setValue(PROP_SHOW_COMPACT_EXECUTION_TREE, showCompactExecutionTree);
   }
   
   /**
    * Sets the default value of property {@link #PROP_SHOW_COMPACT_EXECUTION_TREE}.
    * @param showCompactExecutionTree The new value to set.
    */
   public static void setDefaultShowCompactExecutionTree(boolean showCompactExecutionTree) {
      getStore().setDefault(PROP_SHOW_COMPACT_EXECUTION_TREE, showCompactExecutionTree);
   }

   /**
    * Toggles the value of {@link #isShowCompactExecutionTree()} and updates
    * the tree viewers in all debug views.
    */
   public static void toggleShowCompactExecutionTreePreference() {
      // Toggle preference
      setShowCompactExecutionTree(!isShowCompactExecutionTree());
      // Update all debug tree viewer in the user interface
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            for (IWorkbenchWindow window : PlatformUI.getWorkbench().getWorkbenchWindows()) {
               for (IWorkbenchPage page : window.getPages()) {
                  for (IViewReference reference : page.getViewReferences()) {
                     IWorkbenchPart part = reference.getPart(true);
                     IDebugView view = (IDebugView)part.getAdapter(IDebugView.class);
                     if (view != null) {
                        view.getViewer().refresh();
                     }
                  }
               }
            }
         }
      });
   }
   
   /**
    * Returns the current value.
    * @param type The {@link ISEDAnnotationType} to get its value.
    * @return The current value.
    */
   public static boolean isAnnotationTypeHighlightBackground(ISEDAnnotationType type) {
      return getStore().getBoolean(PROP_ANNOTATION_TYPE_HIGHLIGHT_BACKGROUND_PREFIX + type.getTypeId());
   }
   
   /**
    * Returns the default value.
    * @param type The {@link ISEDAnnotationType} to get its value.
    * @return The default value.
    */
   public static boolean isDefaultAnnotationTypeHighlightBackground(ISEDAnnotationType type) {
      return getStore().getDefaultBoolean(PROP_ANNOTATION_TYPE_HIGHLIGHT_BACKGROUND_PREFIX + type.getTypeId());
   }
   
   /**
    * Sets the current value.
    * @param type The {@link ISEDAnnotationType} to set its value.
    * @param value The new value to set.
    */
   public static void setAnnotationTypeHighlightBackground(ISEDAnnotationType type, boolean value) {
      getStore().setValue(PROP_ANNOTATION_TYPE_HIGHLIGHT_BACKGROUND_PREFIX + type.getTypeId(), value);
   }
   
   /**
    * Sets the default value.
    * @param type The {@link ISEDAnnotationType} to set its value.
    */
   public static void setDefaultAnnotationTypeHighlightBackground(ISEDAnnotationType type) {
      getStore().setDefault(PROP_ANNOTATION_TYPE_HIGHLIGHT_BACKGROUND_PREFIX + type.getTypeId(), type.isDefaultHighlightBackground());
   }
   
   /**
    * Returns the current value.
    * @param type The {@link ISEDAnnotationType} to get its value.
    * @return The current value.
    */
   public static RGB getAnnotationTypeBackgroundColor(ISEDAnnotationType type) {
      return PreferenceConverter.getColor(getStore(), PROP_ANNOTATION_TYPE_BACKGROUND_COLOR_PREFIX + type.getTypeId());
   }
   
   /**
    * Returns the default value.
    * @param type The {@link ISEDAnnotationType} to get its value.
    * @return The default value.
    */
   public static RGB getDefaultAnnotationTypeBackgroundColor(ISEDAnnotationType type) {
      return PreferenceConverter.getDefaultColor(getStore(), PROP_ANNOTATION_TYPE_BACKGROUND_COLOR_PREFIX + type.getTypeId());
   }
   
   /**
    * Sets the current value.
    * @param type The {@link ISEDAnnotationType} to set its value.
    * @param value The new value to set.
    */
   public static void setAnnotationTypeBackgroundColor(ISEDAnnotationType type, RGB value) {
      PreferenceConverter.setValue(getStore(), PROP_ANNOTATION_TYPE_BACKGROUND_COLOR_PREFIX + type.getTypeId(), value);
   }
   
   /**
    * Sets the default value.
    * @param type The {@link ISEDAnnotationType} to set its value.
    */
   public static void setDefaultAnnotationTypeBackgroundColor(ISEDAnnotationType type) {
      PreferenceConverter.setDefault(getStore(), PROP_ANNOTATION_TYPE_BACKGROUND_COLOR_PREFIX + type.getTypeId(), type.getDefaultBackgroundColor());
   }
   
   /**
    * Returns the current value.
    * @param type The {@link ISEDAnnotationType} to get its value.
    * @return The current value.
    */
   public static boolean isAnnotationTypeHighlightForeground(ISEDAnnotationType type) {
      return getStore().getBoolean(PROP_ANNOTATION_TYPE_HIGHLIGHT_FOREGROUND_PREFIX + type.getTypeId());
   }
   
   /**
    * Returns the default value.
    * @param type The {@link ISEDAnnotationType} to get its value.
    * @return The default value.
    */
   public static boolean isDefaultAnnotationTypeHighlightForeground(ISEDAnnotationType type) {
      return getStore().getDefaultBoolean(PROP_ANNOTATION_TYPE_HIGHLIGHT_FOREGROUND_PREFIX + type.getTypeId());
   }
   
   /**
    * Sets the current value.
    * @param type The {@link ISEDAnnotationType} to set its value.
    * @param value The new value to set.
    */
   public static void setAnnotationTypeHighlightForeground(ISEDAnnotationType type, boolean value) {
      getStore().setValue(PROP_ANNOTATION_TYPE_HIGHLIGHT_FOREGROUND_PREFIX + type.getTypeId(), value);
   }
   
   /**
    * Sets the default value.
    * @param type The {@link ISEDAnnotationType} to set its value.
    */
   public static void setDefaultAnnotationTypeHighlightForeground(ISEDAnnotationType type) {
      getStore().setDefault(PROP_ANNOTATION_TYPE_HIGHLIGHT_FOREGROUND_PREFIX + type.getTypeId(), type.isDefaultHighlightForeground());
   }
   
   /**
    * Returns the current value.
    * @param type The {@link ISEDAnnotationType} to get its value.
    * @return The current value.
    */
   public static RGB getAnnotationTypeForegroundColor(ISEDAnnotationType type) {
      return PreferenceConverter.getColor(getStore(), PROP_ANNOTATION_TYPE_FOREGROUND_COLOR_PREFIX + type.getTypeId());
   }
   
   /**
    * Returns the default value.
    * @param type The {@link ISEDAnnotationType} to get its value.
    * @return The default value.
    */
   public static RGB getDefaultAnnotationTypeForegroundColor(ISEDAnnotationType type) {
      return PreferenceConverter.getDefaultColor(getStore(), PROP_ANNOTATION_TYPE_FOREGROUND_COLOR_PREFIX + type.getTypeId());
   }
   
   /**
    * Sets the current value.
    * @param type The {@link ISEDAnnotationType} to set its value.
    * @param value The new value to set.
    */
   public static void setAnnotationTypeForegroundColor(ISEDAnnotationType type, RGB value) {
      PreferenceConverter.setValue(getStore(), PROP_ANNOTATION_TYPE_FOREGROUND_COLOR_PREFIX + type.getTypeId(), value);
   }
   
   /**
    * Sets the default value.
    * @param type The {@link ISEDAnnotationType} to set its value.
    */
   public static void setDefaultAnnotationTypeForegroundColor(ISEDAnnotationType type) {
      PreferenceConverter.setDefault(getStore(), PROP_ANNOTATION_TYPE_FOREGROUND_COLOR_PREFIX + type.getTypeId(), type.getDefaultForegroundColor());
   }
}