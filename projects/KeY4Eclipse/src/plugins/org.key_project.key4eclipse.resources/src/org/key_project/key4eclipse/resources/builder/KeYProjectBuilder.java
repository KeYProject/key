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

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
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
   final static MutexRule mutexRule = new MutexRule();
   private static boolean clean = false;
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IProject project = getProject();
      IResourceDelta delta = getDelta(project);
      if(delta != null || clean){
         KeYProjectDeltaManager deltaManager = KeYProjectDeltaManager.getInstance();
         deltaManager.update(delta);
         KeYProjectDelta keyDelta = deltaManager.getDelta(project);
         if(KeYProjectProperties.isEnableBuildProofs(project) && (keyDelta.isBuildRequired() || !KeYProjectProperties.isEnableBuildRequiredProofsOnly(project))){
            IJobManager jobMan = Job.getJobManager();
            Job[] jobs = jobMan.find("KeYProjectBuildJob");
   
            if(KeYProjectProperties.isEnableAutoInterruptBuild(project)){
               for(Job job : jobs){
                  if(Job.RUNNING == job.getState()){
                     job.cancel();
                     break;
                  }
               }
            }
            
            if(jobs.length <= 1){
               KeYProjectBuildJob proofManagerJob = new KeYProjectBuildJob("KeY Resources build", project);
               proofManagerJob.setRule(KeYProjectBuilder.mutexRule);
               proofManagerJob.schedule();
            }
         }
      }
      return null;
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void clean(IProgressMonitor monitor) throws CoreException {
      IProject project = getProject();
      IFolder mainProofFolder = ResourcesPlugin.getWorkspace().getRoot().getFolder(project.getFullPath().append(KeYResourcesUtil.PROOF_FOLDER_NAME));
      if(mainProofFolder != null){
         mainProofFolder.delete(true, null);
      }
      clean = true;
   }
   
   
   
}