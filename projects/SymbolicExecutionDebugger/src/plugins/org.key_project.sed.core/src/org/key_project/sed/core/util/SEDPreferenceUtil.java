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

package org.key_project.sed.core.util;

import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.key_project.sed.core.Activator;

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
}