package org.key_project.key4eclipse.resources.ui.handlers;

import java.io.File;
import java.util.List;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.texteditor.ITextEditor;
import org.key_project.key4eclipse.common.ui.dialog.ContractSelectionDialog;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.common.ui.provider.ImmutableCollectionContentProvider;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuildInstruction;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuilder;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

public class BuildProofTextSelectionHandler extends AbstractSaveExecutionHandler {

   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      if (selection instanceof ITextSelection) {
         IEditorPart editor = HandlerUtil.getActiveEditor(event);
         if(editor != null && editor instanceof ITextEditor){
            IEditorInput editorInput = editor.getEditorInput();
            if(editorInput != null){
               IJavaElement javaElement = JavaUI.getEditorInputJavaElement(editor.getEditorInput());
               if(javaElement != null && javaElement instanceof ICompilationUnit){
                  try {
                     ICompilationUnit compUnit = (ICompilationUnit) javaElement;
                     ISelection editorSelection = ((ITextEditor) editor).getSelectionProvider().getSelection();
                     if(editorSelection instanceof ITextSelection){
                        IJavaElement selectedElement = compUnit.getElementAt(((ITextSelection) editorSelection).getOffset());
                        if(selectedElement != null && IJavaElement.METHOD == selectedElement.getElementType()){
                           IMethod method = (IMethod) selectedElement;
                           IResource res = method.getResource();
                           if(res != null && res instanceof IFile){
                              IFile javaFile = (IFile) res;
                              ContractSelectionJob csj = new ContractSelectionJob("Select Contract", javaFile, method);
                              csj.schedule();
                           }
                        }
                     }
                  } catch (Exception e){
                     LogUtil.getLogger().logError(e);
                  }
               }
            }
         }
      }
      return null;
   }

   
   private class ContractSelectionJob extends Job{
   
      private IFile javaFile;
      private IProject project;
      private IMethod method;
      
      public ContractSelectionJob(String name, IFile javaFile, IMethod method) {
         super(name);
         this.javaFile = javaFile;
         this.project = javaFile.getProject();
         this.method = method;
      }
   
      @Override
      protected IStatus run(IProgressMonitor monitor) {
         try{
            File location = KeYUtil.getSourceLocation(project);
            File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
            List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
            final KeYEnvironment<CustomUserInterface> environment = KeYEnvironment.load(location, classPaths, bootClassPath);
            if(environment != null && environment.getInitConfig() != null) {
               // Get method to proof in KeY
               final IProgramMethod pm = KeYUtil.getProgramMethod(method, environment.getJavaInfo());
               if (pm != null) {
                  KeYJavaType type = pm.getContainerType();
                  final ImmutableSet<FunctionalOperationContract> contracts = environment.getSpecificationRepository().getOperationContracts(type, pm);
                  if(contracts != null){
                     Runnable run = new Runnable() {
                        @Override
                        public void run() {
                           try{
                              Contract contract = openDialog(contracts, environment);
                              if(contract != null){
                                 IFolder proofFolder = KeYResourcesUtil.getProofFolder(javaFile);
                                 IFile proofFile = KeYResourcesUtil.getProofFile(contract.getName(), proofFolder.getFullPath());
                                 KeYProjectBuildInstruction inst = new KeYProjectBuildInstruction(project, false);
                                 inst.addElementToBuild(proofFile);
                                 KeYProjectBuilder.buildsToDo.add(inst);
                                 try {
                                    inst.getProject().build(IncrementalProjectBuilder.FULL_BUILD, new NullProgressMonitor());
                                 }
                                 catch (CoreException e) {
                                    KeYProjectBuilder.buildsToDo.remove(inst);
                                    LogUtil.getLogger().logError(e);
                                 }
                              }
                           } catch (ProofInputException e){
                              LogUtil.getLogger().logError(e);
                           }
                        }
                     };
                     Display.getDefault().asyncExec(run);  
                  }
               }
               else {
                  return LogUtil.getLogger().createErrorStatus("Can't find method \"" + JDTUtil.getQualifiedMethodLabel(method) + "\" in KeY.");
               }
            }
            return Status.OK_STATUS; 
         } catch (Exception e){
            LogUtil.getLogger().logError(e);
            return Status.CANCEL_STATUS;
         }
         finally {
            monitor.done();
         }
      }
      
      
      private Contract openDialog(ImmutableSet<? extends Contract> contracts, KeYEnvironment<?> environment) throws ProofInputException{
         Shell parent = WorkbenchUtil.getActiveShell();
         ImmutableCollectionContentProvider contentProvider = ImmutableCollectionContentProvider.getInstance();
         ContractSelectionDialog dialog = new ContractSelectionDialog(parent, contentProvider, environment.getServices());
         dialog.setTitle("Select contract to build with KeY Resources");
         dialog.setMessage("Select contract to build.");
         dialog.setInput(contracts);
         if(!contracts.isEmpty()){
            dialog.setInitialSelections(new Contract[] {CollectionUtil.getFirst(contracts)});
         }
         if (dialog.open() == ContractSelectionDialog.OK) {
             Object result = dialog.getFirstResult();
             if (result != null && result instanceof Contract) {
                 return (Contract) result;
                 
             }
             else {
                 throw new ProofInputException("The selected contract is no FunctionalOperationContract.");
             }
         }
         else {
            return null;
         }
      }
   }
}
