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

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.key_project.key4eclipse.common.ui.testGeneration.EclipseTestGenerator;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * Rule to avoid multiple {@link KeYProjectBuildJob}s run simultaneously.
 * @author Stefan Käsdorf
 */
public class KeYProjectBuildMutexRule implements ISchedulingRule{
   
   private List<IProject> projects;
   
   public KeYProjectBuildMutexRule(IProject... projects){
      this.projects = new LinkedList<IProject>();
      for(IProject project : projects) {
         this.projects.add(project);
         if(KeYProjectProperties.isGenerateTestCases(project)) {
            IProject testProject = ResourcesPlugin.getWorkspace().getRoot().getProject(project.getName() + EclipseTestGenerator.TEST_PROJECT_SUFFIX);
            this.projects.add(testProject);
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean contains(ISchedulingRule rule) {
      if(rule != null){
         if(rule instanceof IFolder || rule instanceof IFile){
            IResource ruleResource = (IResource) rule;
            IProject ruleProject = ruleResource.getProject();
            if(projects.contains(ruleProject)) {
               if(KeYResourcesUtil.isKeYProject(ruleProject)){
                  IFolder proofFolder = ruleResource.getProject().getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
                  if(proofFolder.exists()){
                     return proofFolder.getFullPath().isPrefixOf(ruleResource.getFullPath());
                  }
               }
               else {
                  return true;
               }
            }
            return false;
         }
         else if(rule instanceof IProject){
            return projects.contains((IProject) rule);
         }
      }
      return (rule == this);
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isConflicting(ISchedulingRule rule) {
      return ((rule instanceof KeYProjectBuildMutexRule) || contains(rule)) ;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getClass().getSimpleName() + " (" + ArrayUtil.toString(projects.toArray()) + ")";
   }
}
