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

package org.key_project.javaeditor;

import java.util.List;

import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.key_project.javaeditor.management.JavaEditorManager;
import org.key_project.javaeditor.util.IPreferenceListener;
import org.key_project.javaeditor.util.PreferenceUtil;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "org.key_project.javaeditor"; //$NON-NLS-1$

	// The shared instance
	private static Activator plugin;

	/**
	 * Listens for changes on {@link #getPreferenceStore()}.
	 */
	private final IPropertyChangeListener preferenceChangeListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent event) {
         handlePreferenceChanged(event);
      }
   };
	
	/**
	 * The constructor
	 */
	public Activator() {
	}

   /*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
	   getPreferenceStore().addPropertyChangeListener(preferenceChangeListener);
		super.start(context);
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
	   getPreferenceStore().removePropertyChangeListener(preferenceChangeListener);
      JavaEditorManager.getInstance().dispose();
		plugin = null;
		super.stop(context);
	}

	/**
	 * When a property of {@link #getPreferenceStore()} has changed.
	 * @param event The {@link PropertyChangeEvent}.
	 */
   protected void handlePreferenceChanged(PropertyChangeEvent event) {
      if (PreferenceUtil.PROP_EXTENSIONS_ENABLED.equals(event.getProperty())) {
         List<IPreferenceListener> listener = PreferenceUtil.createListener();
         for (IPreferenceListener l : listener) {
            l.extensionsEnabledStateChanged(PreferenceUtil.isExtensionsEnabled());
         }
      }
      else if (event.getProperty().startsWith(PreferenceUtil.PROP_EXTENSION_ENABLED_PREFIX)) {
         String id = event.getProperty().substring(PreferenceUtil.PROP_EXTENSION_ENABLED_PREFIX.length());
         List<IPreferenceListener> listener = PreferenceUtil.createListener();
         for (IPreferenceListener l : listener) {
            l.extensionEnabledStateChanged(id, PreferenceUtil.isExtensionEnabled(id));
         }
      }
   }

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return plugin;
	}

}
