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

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.jobs.IJobManager;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;

/**
 * The KeYProject builder.
 * @author Stefan Käsdorf
 */
public class KeYProjectBuilder extends IncrementalProjectBuilder {

   
   /**
    * The builder id.
    */
   public final static String BUILDER_ID = "org.key_project.key4eclipse.resources.KeYProjectBuilder";
   public static List<KeYProjectBuildInstruction> buildsToDo = Collections.synchronizedList(new LinkedList<KeYProjectBuildInstruction>());
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IProject project = getProject();
      if(KeYProjectProperties.isEnableKeYResourcesBuilds(project)){
         IResourceDelta delta = getDelta(project);
         KeYProjectBuildInstruction inst = getBuildInstruction(project);
         if(isBuildRequired(project, delta) || inst != null){
            List<KeYProjectBuildJob> projectBuildJobs = getProjectBuildJobs(project);
            boolean interrupt = interruptBuild(project, inst);
            if(interrupt){
               for(Job job : projectBuildJobs){
                  if(Job.RUNNING == job.getState()){
                     job.cancel();
                     break;
                  }
               }
            }
            
            if(projectBuildJobs.size() <= 1 || inst != null){
               if(inst == null){
                  inst = new KeYProjectBuildInstruction(project, false);
               }
               KeYProjectBuildJob proofManagerJob = new KeYProjectBuildJob("KeY Resources build", project, inst);
               proofManagerJob.setRule(new MutexRule(project));
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
      KeYProjectBuilder.buildsToDo.add(new KeYProjectBuildInstruction(getProject(), true));
   }
   
   
   private KeYProjectBuildInstruction getBuildInstruction(IProject project) {
      if(project != null){
         for(KeYProjectBuildInstruction inst : buildsToDo){
            if(project.equals(inst.getProject())){
               buildsToDo.remove(inst);
               return inst;
            }
         }
      }
      return null;
   }
   
     
   /**
    * Checks if a new Build is required based on the {@link KeYProjectProperties}, the {@link KeYProjectDelta} and the outdated {@link IMarker}.
    * @param project - the {@link IProject} to check
    * @param delta - the new {@link IResourceDelta} of the given {@link IProject}
    * @return true if a new build is required
    */
   private boolean isBuildRequired(IProject project, IResourceDelta delta){
      KeYProjectDelta keyDelta = null;
      if(delta != null){
         KeYProjectDeltaManager deltaManager = KeYProjectDeltaManager.getInstance();
         deltaManager.update(delta);
         keyDelta = deltaManager.getDelta(project);
      }
      if(keyDelta != null && keyDelta.isBuildRequired()){
         return true;
      }
      return false;
   }
   
   
   private boolean interruptBuild(IProject project, KeYProjectBuildInstruction inst){
      if(KeYProjectProperties.isEnableAutoInterruptBuild(project)){
         KeYProjectDeltaManager deltaManager = KeYProjectDeltaManager.getInstance();
         KeYProjectDelta keyDelta = deltaManager.getDelta(project);
         if((inst != null && inst.getClean()) || keyDelta.isBuildRequired()){
            return true;
         }
      }
      return false;
   }
   
   
   private List<KeYProjectBuildJob> getProjectBuildJobs(IProject project){
      List<KeYProjectBuildJob> projectKeYJobs = new LinkedList<KeYProjectBuildJob>();
      if(project != null){
         IJobManager jobMan = Job.getJobManager();
         Job[] jobs = jobMan.find("KeYProjectBuildJob");
         for(Job job : jobs){
            if(job instanceof KeYProjectBuildJob){
               KeYProjectBuildJob keyJob = (KeYProjectBuildJob) job;
               if(project.equals(keyJob.getProject())){
                  projectKeYJobs.add(keyJob);
               }
            }
         }
      }
      return projectKeYJobs;
   }
}