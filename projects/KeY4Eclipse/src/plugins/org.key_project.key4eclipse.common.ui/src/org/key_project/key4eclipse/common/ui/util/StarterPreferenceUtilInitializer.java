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

package org.key_project.key4eclipse.common.ui.util;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.key_project.key4eclipse.common.ui.starter.IFileStarter;
import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.common.ui.starter.IProjectStarter;

import de.uka.ilkd.key.collection.ImmutableList;

/**
 * Initializes the default preferences accessible via {@link StarterPreferenceUtil}.
 * @author Martin Hentschel
 */
public class StarterPreferenceUtilInitializer extends AbstractPreferenceInitializer {
   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeDefaultPreferences() {
      // Global starter
      ImmutableList<StarterDescription<IGlobalStarter>> globalStarters = StarterUtil.getGlobalStarters();
      if (!globalStarters.isEmpty()) {
         StarterPreferenceUtil.setDefaultSelectedGlobalStarterID(globalStarters.head().getId());
      }
      StarterPreferenceUtil.setDefaultDontAskForGlobalStarter(globalStarters.size() == 1);
      StarterPreferenceUtil.setDefaultGlobalStarterDisabled(false);
      // Method starter
      ImmutableList<StarterDescription<IMethodStarter>> methodStarters = StarterUtil.getMethodStarters();
      if (!methodStarters.isEmpty()) {
         StarterPreferenceUtil.setDefaultSelectedMethodStarterID(methodStarters.head().getId());
      }
      StarterPreferenceUtil.setDefaultDontAskForMethodStarter(methodStarters.size() == 1);
      StarterPreferenceUtil.setDefaultMethodStarterDisabled(false);
      // File starter
      ImmutableList<StarterDescription<IFileStarter>> fileStarters = StarterUtil.getFileStarters();
      if (!fileStarters.isEmpty()) {
         StarterPreferenceUtil.setDefaultSelectedFileStarterID(fileStarters.head().getId());
      }
      StarterPreferenceUtil.setDefaultDontAskForFileStarter(fileStarters.size() == 1);
      StarterPreferenceUtil.setDefaultFileStarterDisabled(false);
      // Project starter
      ImmutableList<StarterDescription<IProjectStarter>> projectStarters = StarterUtil.getProjectStarters();
      if (!projectStarters.isEmpty()) {
         StarterPreferenceUtil.setDefaultSelectedProjectStarterID(projectStarters.head().getId());
      }
      StarterPreferenceUtil.setDefaultDontAskForProjectStarter(projectStarters.size() == 1);
      StarterPreferenceUtil.setDefaultProjectStarterDisabled(false);
   }
}