package org.key_project.key4eclipse.resources.ui.handlers;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildJob;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildMutexRule;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.util.LinkedHashMap;

@SuppressWarnings("restriction")
public class ManualBuildHandler extends AbstractSaveExecutionHandler {

   private HashMap<IProject, List<Object>> selectedElements = new LinkedHashMap<IProject, List<Object>>();
   
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
            List<Object> subSelectedElements = null;
            if (obj instanceof IJavaProject) {
               IProject p = ((IJavaProject) obj).getProject();
               if (KeYProjectProperties.isEnableKeYResourcesBuilds(p) && KeYResourcesUtil.isKeYProject(p)) {
                  project = p;
               }
            }
            else if(obj instanceof IPackageFragmentRoot || obj instanceof IPackageFragment){
               IPackageFragment packageFragment = (IPackageFragment) obj;
               if(packageFragment.containsJavaResources()){
                  IResource res = packageFragment.getResource();
                  if(res != null && res.exists() && res.getType() == IResource.FOLDER){
                     IProject p = res.getProject();
                     if(p != null && KeYResourcesUtil.isKeYProject(p)){
                        IFolder folder = (IFolder) res;
                        IResource[] members = folder.members();
                        for(IResource member : members){
                           if(member != null && member.exists() && member.getType() == IResource.FILE){
                              IJavaElement element = JavaCore.create(member);
                              if (element instanceof ICompilationUnit) {
                                 if(project == null){
                                    project = p;
                                 }
                                 if(subSelectedElements == null){
                                    subSelectedElements = new LinkedList<Object>();
                                 }
                                 subSelectedElements.add(member);
                              }
                           }
                        }
                     }
                  }
               }
            }
            else if(obj instanceof ICompilationUnit){
               IResource res = ((ICompilationUnit) obj).getResource();
               if(res != null && res.exists() && res.getType() == IResource.FILE){
                  IProject p = res.getProject();
                  if(p != null && KeYResourcesUtil.isKeYProject(p)){
                     project = p;
                     subSelectedElements = new LinkedList<Object>();
                     subSelectedElements.add(res);
                  }
               }
            }
            else if(obj instanceof IType){
               IType type = (IType) obj;
               IProject p = type.getResource().getProject();
               if(p != null && KeYResourcesUtil.isKeYProject(p)){
                  IMethod[] methods = type.getMethods();
                  if(methods.length > 0){
                     project = p;
                     subSelectedElements = new LinkedList<Object>();
                     subSelectedElements.addAll(KeYResourcesUtil.arrayToList(methods));
                  }
               }
            }
            else if (obj instanceof IMethod) {
               IMethod method = (IMethod) obj;
               IProject p = method.getResource().getProject();
               if(p != null && KeYResourcesUtil.isKeYProject(p)){
                  project = p;
                  subSelectedElements = new LinkedList<Object>();
                  subSelectedElements.add(method);
               }
            }
            else if(obj instanceof IFolder){
               IFolder folder = (IFolder) obj;
               IProject p = folder.getProject();
               if(p != null && KeYResourcesUtil.isKeYProject(p) && KeYResourcesUtil.isInProofFolder(folder)){
                  List<IFile> proofFiles = KeYResourcesUtil.getAllProofFiles(folder);
                  if(!proofFiles.isEmpty()){
                     project = p;
                     subSelectedElements = new LinkedList<Object>();
                     subSelectedElements.addAll(proofFiles);
                  }
               }
            }
            else if (obj instanceof IFile) {
               IFile file = (IFile) obj;
               IProject p = file.getProject();
               if(p != null && KeYResourcesUtil.isKeYProject(p) && KeYResourcesUtil.isProofFile(file)){
                  project = p;
                  subSelectedElements = new LinkedList<Object>();
                  subSelectedElements.add(file);
               }
            }
            addToSelectedElements(project, subSelectedElements);
         }
      }
      else if(selection instanceof ITextSelection){
         ITextSelection textSelection = (ITextSelection) selection;
         IEditorPart editor = HandlerUtil.getActiveEditor(event);
         if(editor instanceof CompilationUnitEditor){
            IEditorInput editorInput = editor.getEditorInput();
            if(editorInput != null && editorInput instanceof IFileEditorInput){
               IJavaElement javaElement = JavaUI.getEditorInputJavaElement(editorInput);
               if(javaElement != null && javaElement instanceof ICompilationUnit){
                  ICompilationUnit compUnit = (ICompilationUnit) javaElement;
                  IJavaElement selectedElement = compUnit.getElementAt(textSelection.getOffset());
                  if(selectedElement != null && selectedElement.getElementType() == IJavaElement.METHOD){
                     IProject project = compUnit.getResource().getProject();
                     if(project != null && KeYResourcesUtil.isKeYProject(project)){
                        List<Object> subSelected = new LinkedList<Object>();
                        subSelected.add(selectedElement);
                        addToSelectedElements(project, subSelected);
                     }
                  }
               }
            }
         }
      }
      for(Map.Entry<IProject, List<Object>> entry : selectedElements.entrySet()){
         IProject p = entry.getKey();
         List<Object> value = entry.getValue();
         KeYProjectBuildJob buildJob = null;
         if(KeYProjectBuildJob.BUILD_ALL_PROOFS_COMMAND_ID.equals(event.getCommand().getId())){
            buildJob = new KeYProjectBuildJob(p, KeYProjectBuildJob.MANUAL_BUILD_ALL_PROOFS, value);
         }
         if(KeYProjectBuildJob.BUILD_OUTDATED_PROOFS_COMMAND_ID.equals(event.getCommand().getId())){
            buildJob = new KeYProjectBuildJob(p, KeYProjectBuildJob.MANUAL_BUILD_OUTDATED_PROOFS, value);
         }
         if(buildJob != null){
            buildJob.setRule(new KeYProjectBuildMutexRule(p));
            buildJob.schedule();
         }
      }
      return null;
   }
   
   
   private void addToSelectedElements(IProject project, List<Object> subSelected){
      if(project != null){
         if(subSelected == null){
            selectedElements.put(project, null);
         }
         else if(!subSelected.isEmpty()){
            List<Object> mapping = null;
            if(!selectedElements.containsKey(project)){
               mapping = new LinkedList<Object>();
            }
            else if(selectedElements.containsKey(project) && selectedElements.get(project) != null){
               mapping = selectedElements.get(project);
            }
            if(mapping != null){
               for(Object obj : subSelected){
                  if(!mapping.contains(obj)){
                     mapping.add(obj);
                  }
               }
               selectedElements.put(project, mapping);
            }
         }
      }
   }
}
