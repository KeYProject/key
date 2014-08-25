package org.key_project.key4eclipse.resources.builder;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.ui.IStartup;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.LogUtil;


public class KeYResourcesStartup implements IStartup {

   @Override
   public void earlyStartup() {
      try{
         IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
         IProject[] projects = root.getProjects();
         List<IProject> keyProjects = new LinkedList<IProject>();
         for(IProject project : projects){         
            if(KeYProjectProperties.isEnableKeYResourcesBuilds(project) && KeYProjectProperties.isEnableBuildOnStartup(project)){
               if(project != null && project.exists() && project.isOpen()){
                  IProjectDescription desc = project.getDescription();
                  if(desc.hasNature("org.key_project.key4eclipse.resources.KeYProjectNature")){
                     keyProjects.add(project);
                  }
               }
            }
         }
         for(IProject keyProject : keyProjects){
            KeYProjectBuilder.buildsToDo.add(new KeYProjectBuildInstruction(keyProject, false));
            keyProject.build(IncrementalProjectBuilder.FULL_BUILD, new NullProgressMonitor());
         }
      } catch (CoreException e){
         LogUtil.getLogger().logError(e);
      }
   }
}
