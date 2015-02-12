package org.key_project.key4eclipse.resources.builder;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.ui.IStartup;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;


public class KeYResourcesStartup implements IStartup {

   @Override
   public void earlyStartup() {
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IProject[] projects = root.getProjects();
      List<IProject> keyProjects = new LinkedList<IProject>();
      for(IProject project : projects){         
         if (KeYResourcesUtil.isKeYProject(project) && 
             KeYProjectProperties.isEnableKeYResourcesBuilds(project) && 
             KeYProjectProperties.isEnableBuildOnStartup(project)) {
            keyProjects.add(project);
         }
      }
      for(IProject keyProject : keyProjects){
         KeYResourcesUtil.synchronizeProject(keyProject);
         KeYProjectBuildJob proofManagerJob = new KeYProjectBuildJob(keyProject, KeYProjectBuildJob.STARTUP_BUILD);
         proofManagerJob.setRule(new KeYProjectBuildMutexRule(keyProject));
         proofManagerJob.schedule();
      }
   }
}
