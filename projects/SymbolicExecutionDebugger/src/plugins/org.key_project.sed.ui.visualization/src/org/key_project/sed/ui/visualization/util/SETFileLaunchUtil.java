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

package org.key_project.sed.ui.visualization.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.key_project.sed.core.util.LaunchUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

/**
 * Provides constants and functionality to launch SET files.
 * @author Martin Hentschel
 */
public final class SETFileLaunchUtil {
   /**
    * The ID of the launch configuration type.
    */
   public static final String LAUNCH_CONFIGURATION_TYPE_ID = "org.key_project.sed.ui.visualization.setFile";

   /**
    * The key of the attribute "file" in an {@link ILaunchConfiguration} of type {@value SETFileLaunchUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
    */
   public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_FILE_TO_LOAD = "org.key_project.sed.ui.visualization.setFile.attribute.fileToLoad";

   /**
    * The launch mode supported by the Symbolic Execution Debugger based on KeY.
    */
   public static final String MODE = "debug";

   /**
    * Constructor to forbid instances.
    */
   private SETFileLaunchUtil() {
   }
   
   /**
    * Creates a new {@link ILaunchConfiguration}.
    * @param file The {@link IFile} to launch.
    * @return The new created {@link ILaunchConfiguration}.
    * @throws CoreException Occurred Exception.
    */
   public static ILaunchConfiguration createConfiguration(IFile file) throws CoreException {
       ILaunchConfiguration config = null;
       ILaunchConfigurationWorkingCopy wc = null;
       ILaunchConfigurationType configType = getConfigurationType();
       String path = file.getFullPath().toString();
       String name = file.getName();
       wc = configType.newInstance(null, LaunchUtil.getLaunchManager().generateLaunchConfigurationName(name));
       wc.setAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_FILE_TO_LOAD, path);
       wc.setMappedResources(new IResource[] {file});
       config = wc.doSave();
       return config;
   }
   /**
    * Returns the used {@link ILaunchConfigurationType}.
    * @return The used {@link ILaunchConfigurationType}.
    */
   public static ILaunchConfigurationType getConfigurationType() {
       return LaunchUtil.getConfigurationType(LAUNCH_CONFIGURATION_TYPE_ID);            
   }
   
   /**
    * Searches all {@link ILaunchConfiguration} that handles
    * the given {@link IMethod}.
    * @param method The {@link IMethod} for that {@link ILaunchConfiguration}s are required.
    * @param methodStartPosition An optional start position to execute only parts of the method.
    * @param methodEndPosition An optional end position to execute only parts of the method.
    * @return The found {@link ILaunchConfiguration}s.
    * @throws CoreException Occurred Exception.
    */
   public static List<ILaunchConfiguration> searchLaunchConfigurations(IFile file) throws CoreException {
       // Get parameters
       String path = file != null ? file.getFullPath().toString() : null;
       // Compare existing configurations to with the parameters.
       ILaunchConfiguration[] configs = DebugPlugin.getDefault().getLaunchManager().getLaunchConfigurations(getConfigurationType());
       List<ILaunchConfiguration> result = new ArrayList<ILaunchConfiguration>(configs.length);
       for (ILaunchConfiguration config : configs) {
           // Check file
           if (ObjectUtil.equals(path, getFileToLoadValue(config))) {
              result.add(config);
           }
       }
       return result;
   }

   /**
    * Returns the file to load attribute value from the given {@link ILaunchConfiguration}.
    * @param configuration The {@link ILaunchConfiguration} to read from.
    * @return The file to load attribute value.
    * @throws CoreException Occurred Exception.
    */
   public static String getFileToLoadValue(ILaunchConfiguration configuration) throws CoreException {
      return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_FILE_TO_LOAD, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
   }
}