/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.dbcmodel.diagram.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorPlugin;

/**
 * @generated
 */
public class DiagramPreferenceInitializer extends AbstractPreferenceInitializer {

   /**
    * @generated
    */
   public void initializeDefaultPreferences() {
      IPreferenceStore store = getPreferenceStore();
      DiagramGeneralPreferencePage.initDefaults(store);
      DiagramAppearancePreferencePage.initDefaults(store);
      DiagramConnectionsPreferencePage.initDefaults(store);
      DiagramPrintingPreferencePage.initDefaults(store);
      DiagramRulersAndGridPreferencePage.initDefaults(store);

   }

   /**
    * @generated
    */
   protected IPreferenceStore getPreferenceStore() {
      return DbCDiagramEditorPlugin.getInstance().getPreferenceStore();
   }
}
