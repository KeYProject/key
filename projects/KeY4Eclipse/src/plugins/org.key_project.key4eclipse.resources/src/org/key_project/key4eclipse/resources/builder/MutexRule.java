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

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.jobs.ISchedulingRule;

public class MutexRule implements ISchedulingRule{
      
   @Override
   public boolean contains(ISchedulingRule rule) {
      if(rule != null){
         if(rule instanceof IFolder){
            IFolder ruleFolder = (IFolder) rule;
            IFolder proofFolder = ruleFolder.getProject().getFolder("proofs");
            if(proofFolder.exists()){
               return proofFolder.getFullPath().isPrefixOf(ruleFolder.getFullPath());
            }
            else{
               return false;
            }
         }
         else if(rule instanceof IProject){
            return true;
         }
      }
      return (rule == this);
   }

   @Override
   public boolean isConflicting(ISchedulingRule rule) {
      return (rule == this);
   }

}
