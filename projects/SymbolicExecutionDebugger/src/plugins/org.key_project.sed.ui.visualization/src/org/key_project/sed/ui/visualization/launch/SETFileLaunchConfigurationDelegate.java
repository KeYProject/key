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

package org.key_project.sed.ui.visualization.launch;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLReader;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.sed.ui.visualization.util.SETFileLaunchUtil;

/**
 * This {@link LaunchConfigurationDelegate} is responsible to launch a SET file.
 * @author Martin Hentschel
 */
public class SETFileLaunchConfigurationDelegate extends LaunchConfigurationDelegate {
   /**
    * {@inheritDoc}
    */
   @Override
   public void launch(final ILaunchConfiguration configuration, 
                      String mode, 
                      ILaunch launch, 
                      IProgressMonitor monitor) throws CoreException {
      try {
         // Get file to load
         String path = SETFileLaunchUtil.getFileToLoadValue(configuration);
         Assert.isNotNull(path);
         IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(path));
         Assert.isNotNull(file);
         Assert.isTrue(file.exists());
         // Load file
         SEDXMLReader reader = new SEDXMLReader(launch, false);
         // Configure launch
         List<ISEDDebugTarget> targets = reader.read(file);
         for (ISEDDebugTarget target : targets) {
            launch.addDebugTarget(target);
         }
      }
      catch (CoreException e) {
         throw e;
      }
      catch (Exception e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
      }
   }
}