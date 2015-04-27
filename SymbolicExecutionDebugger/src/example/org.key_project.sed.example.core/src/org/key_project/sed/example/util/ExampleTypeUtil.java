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

package org.key_project.sed.example.util;

import org.eclipse.debug.core.ILaunchConfigurationType;
import org.key_project.sed.core.util.LaunchUtil;

/**
 * This utility class provides static methods to work with the 
 * {@link ILaunchConfigurationType} of the example symbolic execution engine.
 * @author Martin Hentschel
 */
public final class ExampleTypeUtil {
   /**
    * The ID of the {@link ILaunchConfigurationType}.
    */
   private static final String LAUNCH_CONFIGURATION_TYPE_ID = "org.key_project.sed.example.core.exampleLaunchType";

   /**
    * Forbid instances.
    */
   private ExampleTypeUtil() {
   }
   
   /**
    * Returns the {@link ILaunchConfigurationType} of the example symbolic execution engine.
    * @return The {@link ILaunchConfigurationType} of the example symbolic execution engine.
    */
   public static ILaunchConfigurationType getLaunchConfigurationType() {
      return LaunchUtil.getConfigurationType(LAUNCH_CONFIGURATION_TYPE_ID);
   }
}
