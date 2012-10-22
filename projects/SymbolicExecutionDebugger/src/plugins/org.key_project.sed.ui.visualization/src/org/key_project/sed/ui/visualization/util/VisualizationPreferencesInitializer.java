package org.key_project.sed.ui.visualization.util;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;

/**
 * Initializes the preferences of {@link VisualizationPreferences} when they are
 * accessed the first time. This is managed by extension point
 * {@code org.eclipse.core.runtime.preferences}.
 * @author Martin Hentschel
 * @see VisualizationPreferences
 */
public class VisualizationPreferencesInitializer extends AbstractPreferenceInitializer {
   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeDefaultPreferences() {
      VisualizationPreferences.setDefaultSwitchToStateVisualizationPerspective(MessageDialogWithToggle.PROMPT);
   }
}
