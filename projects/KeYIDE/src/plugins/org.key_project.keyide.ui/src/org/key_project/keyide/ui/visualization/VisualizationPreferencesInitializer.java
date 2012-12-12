package org.key_project.keyide.ui.visualization;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;

//TODO: Rename into KeYIDEPreferencesInitializer
public class VisualizationPreferencesInitializer extends AbstractPreferenceInitializer {
   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeDefaultPreferences() {
      VisualizationPreferences.setDefaultSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
   }
}
