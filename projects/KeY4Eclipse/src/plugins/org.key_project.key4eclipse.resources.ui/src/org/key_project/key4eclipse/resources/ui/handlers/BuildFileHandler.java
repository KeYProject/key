package org.key_project.key4eclipse.resources.ui.handlers;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildInstruction;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuilder;


public class BuildFileHandler extends AbstractSaveExecutionHandler {

   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      List<IFile> files = new LinkedList<IFile>();
      IProject project = null;
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      if (selection instanceof IStructuredSelection) {
         Object[] elements = ((IStructuredSelection) selection).toArray();
         for (Object element : elements) {
            if (element instanceof IFile) {
               IFile file = (IFile) element;
               project = file.getProject();
               files.add(file);
            }
            else if(element instanceof ICompilationUnit){
               ICompilationUnit compUnit = (ICompilationUnit) element;
               IResource res = compUnit.getResource();
               if(res instanceof IFile){
                  IFile file = (IFile) res;
                  project = file.getProject();
                  files.add(file);
               }
            }
         }
      }
      if(!files.isEmpty()){
         KeYProjectBuildInstruction inst = new KeYProjectBuildInstruction(project, false);
         inst.addAllElementsToBuild(files);
         KeYProjectBuilder.buildsToDo.add(inst);
         inst.getProject().build(IncrementalProjectBuilder.FULL_BUILD, new NullProgressMonitor());
      }
      return null;
   }

}
