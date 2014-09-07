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
import org.key_project.key4eclipse.resources.log.LogManager;
import org.key_project.key4eclipse.resources.log.LogRecord;
import org.key_project.key4eclipse.resources.log.LogRecordKind;
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
   /**
    * {@inheritDoc}
    */
   @Override
   protected IProject[] build(int kind, Map<String, String> args, IProgressMonitor monitor) throws CoreException {
      IProject project = getProject();
      IResourceDelta delta = getDelta(project);
      final long start = System.currentTimeMillis();
      final boolean onlyRequiredProofs = KeYProjectProperties.isEnableBuildRequiredProofsOnly(project);
      final int numberOfThreads = KeYProjectProperties.getNumberOfThreads(project);
      final boolean enableThreading = KeYProjectProperties.isEnableMultiThreading(project);
      KeYResourcesUtil.synchronizeProject(project);
      KeYProjectDelta keyDelta = KeYProjectDeltaManager.getInstance().getDelta(project);
      keyDelta.update(delta);
      try {
         if(KeYProjectProperties.isEnableKeYResourcesBuilds(project)){ 
            if((IncrementalProjectBuilder.FULL_BUILD == kind || keyDelta.isBuildRequired()) && !keyDelta.isBuilding()){
               keyDelta.setIsBuilding(true);
               int buildType = IncrementalProjectBuilder.FULL_BUILD == kind ? KeYProjectBuildJob.FULL_BUILD : KeYProjectBuildJob.AUTO_BUILD;
               KeYProjectBuildJob proofManagerJob = new KeYProjectBuildJob(project, buildType);
               proofManagerJob.setRule(new KeYProjectBuildMutexRule(project));
               proofManagerJob.schedule();
            }
         }
      }
      finally {
         LogManager.getInstance().log(project, new LogRecord(LogRecordKind.BUILD, start, System.currentTimeMillis() - start, onlyRequiredProofs, enableThreading, numberOfThreads));
      }
      return null;
   }


   /**
    * {@inheritDoc}
    */
   @Override
   protected void clean(IProgressMonitor monitor) throws CoreException {
      IProject project = getProject();
      final long start = System.currentTimeMillis();
      final boolean onlyRequiredProofs = KeYProjectProperties.isEnableBuildRequiredProofsOnly(project);
      final int numberOfThreads = KeYProjectProperties.getNumberOfThreads(project);
      final boolean enableThreading = KeYProjectProperties.isEnableMultiThreading(project);
      LogManager.getInstance().log(project, new LogRecord(LogRecordKind.CLEAN, start, System.currentTimeMillis() - start, onlyRequiredProofs, enableThreading, numberOfThreads));
   }
}