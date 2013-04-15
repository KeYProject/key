package org.key_project.keyide.ui.util;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;

/**
 * Initializes the preferences of {@link KeYIDEPreferences} when they are
 * accessed the first time. This is managed by extension point
 * {@code org.eclipse.core.runtime.preferences}.
 * @author Marco Drebing, Niklas Bunzel, Christoph Schneider, Stefan Käsdorf
 * @see KeYIDEPreferences
 */
public class KeYIDEPreferencesInitializer extends AbstractPreferenceInitializer {
   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeDefaultPreferences() {
      KeYIDEPreferences.setDefaultSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
   }
}
