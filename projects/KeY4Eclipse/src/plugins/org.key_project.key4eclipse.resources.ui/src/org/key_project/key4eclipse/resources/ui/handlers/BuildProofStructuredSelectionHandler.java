package org.key_project.key4eclipse.resources.ui.handlers;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildInstruction;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuilder;


public class BuildProofStructuredSelectionHandler extends AbstractSaveExecutionHandler {

   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      if (selection instanceof IStructuredSelection) {
         List<IMethod> methods = new LinkedList<IMethod>();
         Object[] elements = ((IStructuredSelection) selection).toArray();
         for (Object element : elements) {
            if (element instanceof IMethod) {
               methods.add((IMethod) element);
            }
         }
         List<KeYProjectBuildInstruction> instructions = new LinkedList<KeYProjectBuildInstruction>();
         while(!methods.isEmpty()){
            IMethod method = methods.remove(0);
            IProject project = method.getResource().getProject();
            if(project != null){
               boolean added = false;
               for(KeYProjectBuildInstruction inst : instructions){
                  if(project.equals(inst.getProject())){
                     inst.addElementToBuild(method);
                     added = true;
                  }
               }
               if(!added){
                  KeYProjectBuildInstruction inst = new KeYProjectBuildInstruction(project, false);
                  inst.addElementToBuild(method);
                  instructions.add(inst);
               }
            }
         }
         while(!instructions.isEmpty()){
            KeYProjectBuildInstruction inst = instructions.remove(0);
            KeYProjectBuilder.buildsToDo.add(inst);
            inst.getProject().build(IncrementalProjectBuilder.FULL_BUILD, new NullProgressMonitor());
         }
      }
      return null;
   }

}
