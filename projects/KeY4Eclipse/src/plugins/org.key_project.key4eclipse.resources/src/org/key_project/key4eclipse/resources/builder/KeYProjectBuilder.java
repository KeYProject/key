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

package org.key_project.key4eclipse.resources.builder;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * The KeYProject builder.
 * @author Stefan Käsdorf
 */
public class KeYProjectBuilder extends IncrementalProjectBuilder {

   
   /**
    * The builder id.
    */
   public final static String BUILDER_ID = "org.key_project.key4eclipse.resources.KeYProjectBuilder";
   private int buildType = KeYProjectBuildJob.AUTO_BUILD;
   /**
    * {@inheritDoc}
    */
   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IProject project = getProject();
      IResourceDelta delta = getDelta(project);
      if(IncrementalProjectBuilder.FULL_BUILD == kind){
         buildType = KeYProjectBuildJob.CLEAN_BUILD;
      }
      if(KeYProjectProperties.isEnableKeYResourcesBuilds(project)){
         KeYProjectDeltaManager deltaManager = KeYProjectDeltaManager.getInstance();
         deltaManager.update(delta);
         KeYProjectDelta keyDelta = deltaManager.getDelta(getProject());
         if(keyDelta.isBuildRequired() || IncrementalProjectBuilder.FULL_BUILD == kind || buildType == KeYProjectBuildJob.CLEAN_BUILD){
            if(!KeYProjectProperties.isEnableAutoInterruptBuild(project)){
               int autoBuilds = KeYResourcesUtil.getNumberOfAutoBuildsInQueue(project);
               if(autoBuilds > 0){
                  return null;
               }
            }
            KeYProjectBuildJob proofManagerJob = new KeYProjectBuildJob(project, buildType);
            buildType = KeYProjectBuildJob.AUTO_BUILD;
            proofManagerJob.setRule(new KeYProjectBuildMutexRule(project));
            proofManagerJob.schedule();
         }
      }
      return null;
   }


   /**
    * {@inheritDoc}
    */
   @Override
   protected void clean(IProgressMonitor monitor) throws CoreException {
      buildType = KeYProjectBuildJob.CLEAN_BUILD;
   }
}