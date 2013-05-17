package org.key_project.key4eclipse.resources.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.internal.resources.Project;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.jdt.internal.eval.EvaluationContext;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

public class ConvertJavaToKeYProjectHandler extends AbstractSaveExecutionHandler {

   @SuppressWarnings("restriction")
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      Object[] elements = SWTUtil.toArray(selection);
      for(Object obj : elements){
         if(obj instanceof JavaProject){
            JavaProject javaProject = (JavaProject) obj;
            IProject project = javaProject.getProject();
            IProjectDescription description = project.getDescription();
            String[] natures = description.getNatureIds();
            String[] newNatures = new String[natures.length + 1];
            System.arraycopy(natures,0,newNatures,0,natures.length);
            newNatures[natures.length] = "org.key_project.key4eclipse.resources.KeYProjectNature";
            description.setNatureIds(newNatures);
            project.setDescription(description,null);            
         }
         else if(obj instanceof Project){
            IProject project = (IProject) obj;
            IProjectDescription description = project.getDescription();
            String[] natures = description.getNatureIds();
            String[] newNatures = new String[natures.length + 1];
            System.arraycopy(natures,0,newNatures,0,natures.length);
            newNatures[natures.length] = "org.key_project.key4eclipse.resources.KeYProjectNature";
            description.setNatureIds(newNatures);
            project.setDescription(description,null);      
            
         }
      }
      return null;
   }


}
