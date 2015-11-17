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

package org.key_project.sed.key.evaluation.model.util;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;

/**
 * Initializes the preferences of {@link ServerSettings} when they are
 * accessed the first time. This is managed by extension point
 * {@code org.eclipse.core.runtime.preferences}.
 * @author Martin Hentschel
 * @see ServerSettings
 */
public class ServerPreferencesInitializer extends AbstractPreferenceInitializer {
   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeDefaultPreferences() {
      ServerPreferences.setDefaultHost("sed.se.informatik.tu-darmstadt.de"); // sed.se.informatik.tu-darmstadt.de or 127.0.0.1 (localhost)
      ServerPreferences.setDefaultPort(10947);
   }
}