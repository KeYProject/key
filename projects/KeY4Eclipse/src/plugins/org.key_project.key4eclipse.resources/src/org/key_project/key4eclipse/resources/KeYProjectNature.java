package org.key_project.key4eclipse.resources;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;

public class KeYProjectNature implements IProjectNature  {
   
   private IProject project;

   @Override
   public void configure() throws CoreException {
      System.out.println("Nature: configure()");
      IProjectDescription desc = project.getDescription();
      //get the description of the project basically .project file information
      ICommand[] commands = desc.getBuildSpec();
      // get the build commands already associated with project.
      for (int i = 0; i < commands.length; ++i) {
            if (commands[i].getBuilderName().equals("org.key_project.key4eclipse.resources.KeYProjectBuilder")) {
               return; // Do nothing if Sample builder is already associated with project
            }
      }
      ICommand[] newCommands = new ICommand[commands.length + 1];
      // create a new build command
      System.arraycopy(commands, 0, newCommands, 0, commands.length);
      ICommand command = desc.newCommand();
      command.setBuilderName("org.key_project.key4eclipse.resources.KeYProjectBuilder"); // attach it to sample builder      
      newCommands[newCommands.length - 1] = command;
      desc.setBuildSpec(newCommands);
      project.setDescription(desc, null); // write to .project file
      for(int i = 0; i<project.getDescription().getBuildSpec().length;i++){
         System.out.println(i + ": " + project.getDescription().getBuildSpec()[i].getBuilderName());
      }
   }
      
   @Override
   public void deconfigure() throws CoreException {
      System.out.println("Nature: deconfigure");
      // TODO Auto-generated method stub
      
   }

   @Override
   public IProject getProject() {
      System.out.println("Nature: getProject()");
      // TODO Auto-generated method stub
      return this.project;
   }

   @Override
   public void setProject(IProject project) {
      System.out.println("Nature: setProject");
      // TODO Auto-generated method stub
      this.project = project;
   }

}
