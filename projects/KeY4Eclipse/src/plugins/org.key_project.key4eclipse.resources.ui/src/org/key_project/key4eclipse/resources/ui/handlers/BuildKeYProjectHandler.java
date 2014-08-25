package org.key_project.key4eclipse.resources.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildInstruction;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuilder;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.util.eclipse.swt.SWTUtil;

public class BuildKeYProjectHandler extends AbstractSaveExecutionHandler {

   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      Object[] elements = SWTUtil.toArray(selection);
      for(Object obj : elements){
         if(obj instanceof IJavaProject){
            IJavaProject javaProject = (IJavaProject) obj;
            IProject project = javaProject.getProject();
            if(KeYProjectProperties.isEnableKeYResourcesBuilds(project)){
               IProjectDescription desc = project.getDescription();
               if(desc.hasNature("org.key_project.key4eclipse.resources.KeYProjectNature")){
                  KeYProjectBuilder.buildsToDo.add(new KeYProjectBuildInstruction(project, false));
                  project.build(IncrementalProjectBuilder.FULL_BUILD, new NullProgressMonitor());
               }     
            }
         }            
      }
      return null;
   }
   
}
