package org.key_project.key4eclipse.resources.builder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.ui.IStartup;
import org.key_project.key4eclipse.resources.property.KeYProjectBuildProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * Handles the start of all {@link KeYProjectBuildJob}s at the eclipse startup.
 * @author Stefan Käsdorf
 */
public class KeYResourcesStartup implements IStartup {

   /**
    * {@inheritDoc}
    */
   @Override
   public void earlyStartup() {
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
      IProject[] projects = root.getProjects();
      for(IProject project : projects){         
         if (KeYResourcesUtil.isKeYProject(project)) {
            KeYProjectBuildProperties properties = new KeYProjectBuildProperties(project);
            if(properties.isEnableKeYResourcesBuilds() && properties.isBuildOnStartUp()) {
               KeYResourcesUtil.synchronizeProject(project);
               KeYProjectDelta keyDelta = KeYProjectDeltaManager.getInstance().getDelta(project);
               keyDelta.update(null);
               if(keyDelta.isBuildRequired() || keyDelta.isBuilding()){
                  keyDelta.setIsSettingUp(true);
                  KeYProjectBuildJob proofManagerJob = new KeYProjectBuildJob(project, KeYProjectBuildJob.STARTUP_BUILD, properties);
                  proofManagerJob.setRule(new KeYProjectBuildMutexRule(project));
                  proofManagerJob.schedule();
               }
            }
         }
      }
   }
}
