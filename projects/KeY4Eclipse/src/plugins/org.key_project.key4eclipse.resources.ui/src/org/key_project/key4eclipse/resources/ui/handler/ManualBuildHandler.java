package org.key_project.key4eclipse.resources.ui.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildJob;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildMutexRule;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

public class ManualBuildHandler extends AbstractSaveExecutionHandler {
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      if(selection instanceof IStructuredSelection){
         Object[] elements = SWTUtil.toArray(selection);
         for (Object obj : elements) {
            IProject project = null;
            if (obj instanceof IJavaProject) {
               project = ((IJavaProject) obj).getProject();
            }
            else if(obj instanceof IProject){
               project = (IProject) obj;
            }
            if(project != null && KeYResourcesUtil.isKeYProject(project)){
               KeYResourcesUtil.synchronizeProject(project);
               KeYProjectBuildJob buildJob = new KeYProjectBuildJob(project, KeYProjectBuildJob.MANUAL_BUILD);
               buildJob.setRule(new KeYProjectBuildMutexRule(project));
               buildJob.schedule();
            }
         }
      }
      return null;
   }
}
