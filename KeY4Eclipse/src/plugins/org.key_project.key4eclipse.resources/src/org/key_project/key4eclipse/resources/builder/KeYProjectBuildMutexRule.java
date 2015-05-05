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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * Rule to avoid multiple {@link KeYProjectBuildJob}s run simultaneously.
 * @author Stefan Käsdorf
 */
public class KeYProjectBuildMutexRule implements ISchedulingRule{
   
   private IProject[] projects;
   
   public KeYProjectBuildMutexRule(IProject... projects){
      this.projects = projects;
   }
   
   public IProject[] getProjects(){
      return projects;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean contains(ISchedulingRule rule) {
      if(rule != null){
         if(rule instanceof IFolder || rule instanceof IFile){
            IResource ruleResource = (IResource) rule;
            IFolder proofFolder = ruleResource.getProject().getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
            if(proofFolder.exists()){
               return proofFolder.getFullPath().isPrefixOf(ruleResource.getFullPath());
            }
            return false;
         }
         else if(rule instanceof IProject){
            return ArrayUtil.contains(projects, (IProject) rule);
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
      return getClass().getSimpleName() + " (" + ArrayUtil.toString(projects) + ")";
   }
}
