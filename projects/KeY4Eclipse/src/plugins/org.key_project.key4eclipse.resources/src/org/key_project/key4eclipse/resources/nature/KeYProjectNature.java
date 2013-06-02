/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.key4eclipse.resources.nature;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;
import org.key_project.util.java.ArrayUtil;

public class KeYProjectNature implements IProjectNature  {
   
   public final static String NATURE_ID = "org.key_project.key4eclipse.resources.KeYProjectNature";
   
   private IProject project;

   
   /**
    * {@inheritDoc}
    */
   @Override
   public void configure() throws CoreException {
      IProjectDescription desc = project.getDescription();
      //get the description of the project basically .project file information
      ICommand[] commands = desc.getBuildSpec();
      // get the build commands already associated with project.
      for (int i = 0; i < commands.length; ++i) {
            if (commands[i].getBuilderName().equals("org.key_project.key4eclipse.resources.KeYProjectBuilder")) {
               return; // Do nothing if builder is already associated with project
            }
      }
      // create a new build command
      ICommand command = desc.newCommand();
      command.setBuilderName("org.key_project.key4eclipse.resources.KeYProjectBuilder"); // attach it to sample builder
      ICommand[] newCommands = ArrayUtil.add(commands, command);
      desc.setBuildSpec(newCommands);
      project.setDescription(desc, null); // write to .project file
   }
      
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void deconfigure() throws CoreException {
      
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public IProject getProject() {
      return this.project;
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public void setProject(IProject project) {
      this.project = project;
   }

}