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

package org.key_project.sed.example.ui.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.DebugUITools;
import org.key_project.sed.core.util.LaunchUtil;
import org.key_project.sed.example.util.ExampleTypeUtil;
import org.key_project.sed.ui.util.LaunchUIUtil;

/**
 * Provides static methods to launch the example symbolic execution engine
 * and to create and manage used {@link ILaunchConfiguration}s.
 * @author Martin Hentschel
 */
public class ExampleLaunchUtil {
   /**
    * The supported launch mode.
    */
   public static final String MODE = "debug";
   
   /**
    * The alternatively supported launch mode.
    */
   public static final String SED_EXAMPLES_MODE = "sedExamples";
   
   /**
    * The ID of the launch group with the SED examples.
    */
   public static final String SED_EXAMPLES_LAUNCH_GROUP_ID = "org.key_project.sed.example.ui.sedExamplesLaunchGroup";

   /**
    * Launches the example symbolic execution engine.
    * @throws CoreException Occurred Exception.
    */
   public static void launch() throws CoreException {
      String name = "SED Example Launch";
      ILaunchConfiguration configuration = findLaunchConfiguration(name);
      if (configuration == null) {
         configuration = createConfiguration(name);
      }
      DebugUITools.launch(configuration, MODE);
   }

   /**
    * Creates a new {@link ILaunchConfiguration} with the given name.
    * @param name The name of the launch configuration.
    * @return The created {@link ILaunchConfiguration}.
    * @throws CoreException Occurred Exception.
    */
   public static ILaunchConfiguration createConfiguration(String name) throws CoreException {
      ILaunchConfigurationType configType = ExampleTypeUtil.getLaunchConfigurationType();
      ILaunchConfigurationWorkingCopy wc = configType.newInstance(null, LaunchUtil.getLaunchManager().generateLaunchConfigurationName(name));
      //wc.setAttribute(attributeName, value); // May set other settings used while the symbolic execution engine is launched by the ExampleLaunchConfigurationDelegate
      ILaunchConfiguration configuration = wc.doSave();
      return configuration;
   }

   /**
    * Returns the {@link ILaunchConfiguration} of the given name if available.
    * <p>
    * If multiple {@link ILaunchConfiguration} of the given name are available
    * the user is asked to select one.
    * @param name The name of the launch configuration.
    * @return The found {@link ILaunchConfiguration} or {@code null} if not available.
    * @throws CoreException Occurred Exception.
    */
   public static ILaunchConfiguration findLaunchConfiguration(String name) throws CoreException {
      List<ILaunchConfiguration> candidateConfigs = searchLaunchConfigurations(name);
      int candidateCount = candidateConfigs.size();
      if (candidateCount == 1) {
          return (ILaunchConfiguration)candidateConfigs.get(0);
      }
      else if (candidateCount > 1) {
          ILaunchConfiguration choosen = LaunchUIUtil.chooseConfiguration(candidateConfigs, "Symbolic Execution Debugger (SED)");
          if (choosen == null) {
              throw new OperationCanceledException();
          }
          return choosen;
      }
      else {
          return null;
      }
   }
   
   /**
    * Returns all available {@link ILaunchConfiguration} of the given name.
    * @param name The name of the launch configuration.
    * @return The found {@link ILaunchConfiguration}s.
    * @throws CoreException Occurred Exception.
    */
   public static List<ILaunchConfiguration> searchLaunchConfigurations(String name) throws CoreException {
       ILaunchConfiguration[] configs = DebugPlugin.getDefault().getLaunchManager().getLaunchConfigurations(ExampleTypeUtil.getLaunchConfigurationType());
       List<ILaunchConfiguration> result = new ArrayList<ILaunchConfiguration>(configs.length);
       for (ILaunchConfiguration config : configs) {
          if (config.getName().equals(name)) {
             result.add(config);
          }
       }
       return result;
   }
}
