package org.key_project.sed.core.util;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;

/**
 * Initializes the default preferences accessible via {@link SEDPreferenceUtil}.
 * @author Martin Hentschel
 */
public class SEDPreferenceUtilInitializer extends AbstractPreferenceInitializer {
   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeDefaultPreferences() {
      SEDPreferenceUtil.setDefaultShowCompactExecutionTree(true);
   }
}
