package org.key_project.key4eclipse.resources.builder;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.EditorSelection;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.keyide.ui.editor.KeYEditor;

@SuppressWarnings("restriction")
public class KeYProjectBuildJob extends Job{
   
   public final static String KEY_PROJECT_BUILD_JOB = "KeYProjectBuildJob";
   public final static String KEY_PROJECT_BUILD_JOB_NAME = "KeY Resources build";
   public final static int AUTO_BUILD = 0;
   public final static int CLEAN_BUILD = 1;
   public final static int STARTUP_BUILD = 2;
   public final static int MANUAL_BUILD_ALL_PROOFS = 3;
   public final static int MANUAL_BUILD_OUTDATED_PROOFS = 4;
   public static final String BUILD_ALL_PROOFS_COMMAND_ID = "org.key_project.key4eclipse.resources.ui.buildAllProofsCommand";
   public static final String BUILD_OUTDATED_PROOFS_COMMAND_ID = "org.key_project.key4eclipse.resources.ui.buildOutdatedProofsCommand";

   private IProject project;
   private int buildType;
   private List<Object> proofsToDo;
   private EditorSelection editorSelection;

   public KeYProjectBuildJob(IProject project, int buildType){
      super(KeYProjectBuildJob.KEY_PROJECT_BUILD_JOB_NAME);
      init(project, buildType, null);
   }
   
   public KeYProjectBuildJob(IProject project, int buildType, List<Object> proofsToDo){
      super(KeYProjectBuildJob.KEY_PROJECT_BUILD_JOB_NAME);
      init(project, buildType, proofsToDo);
   }
   
   private void init(IProject project, int buildType, List<Object> proofsToDo){
      this.project = project;
      this.buildType = buildType;
      this.proofsToDo = proofsToDo;
      this.editorSelection = null;
      if(buildType != KeYProjectBuildJob.CLEAN_BUILD && KeYProjectProperties.isEnableKeYResourcesBuilds(project)){
//         this.editorSelection = getEditorSelection();
      }
   }
   
   
   public int getBuildType(){
      return buildType;
   }
   
   
   public IProject getProject(){
      return project;
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean belongsTo(Object family) {
      return KeYProjectBuildJob.KEY_PROJECT_BUILD_JOB.equals(family);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(IProgressMonitor monitor) {
      if(KeYProjectProperties.isEnableKeYResourcesBuilds(project)){
         if(KeYProjectProperties.isEnableAutoInterruptBuild(project)){
            List<KeYProjectBuildJob> projectBuildJobs = KeYResourcesUtil.getProjectBuildJobs(project);
            for(KeYProjectBuildJob job : projectBuildJobs){
               if(Job.RUNNING == job.getState() && job.getBuildType() != KeYProjectBuildJob.CLEAN_BUILD && !this.equals(job)){
                  job.cancel();
               }
            }
         }
         ProofManager proofManager = null;
         try{
            proofManager = new ProofManager(project, buildType, proofsToDo, editorSelection);
            proofManager.runProofs(monitor);
         } catch (Exception e){
            //TODO
            System.out.println("Error");
         }
         finally{
            if(proofManager != null){
               proofManager.dispose();
            }
         }
      }
      return Status.OK_STATUS;
   }
   
   
   private EditorSelection getEditorSelection(){
      final EditorSelection editorSelection = new EditorSelection();
      Display.getDefault().syncExec(new Runnable() {
         
         @Override
         public void run() {
            IWorkbenchWindow activeWorkbenchWindow = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
            if(activeWorkbenchWindow != null){
               IWorkbenchPage activeWorkbenchPage = activeWorkbenchWindow.getActivePage();
               if(activeWorkbenchPage != null){
                  IEditorPart activeEditor = activeWorkbenchPage.getActiveEditor();
                  IEditorReference[] editorRefs = activeWorkbenchPage.getEditorReferences();
                  for(IEditorReference editorRef : editorRefs){
                     if(editorRef != null){
                        IEditorPart editor = editorRef.getEditor(true);
                        if(editor != null && editor instanceof CompilationUnitEditor){
                           IJavaElement javaElement = JavaUI.getEditorInputJavaElement(editor.getEditorInput());
                           if(javaElement != null && javaElement instanceof ICompilationUnit){
                              ICompilationUnit compUnit = (ICompilationUnit) javaElement;
                              IResource res = compUnit.getResource();
                              if(res != null && res.exists() && project.equals(res.getProject()) && res.getType() == IResource.FILE){
                                 if(editor.equals(activeEditor) && editorSelection.getActiveFile() == null){
                                    editorSelection.setActiveFile((IFile) res);
                                    ISelection selection = editor.getEditorSite().getSelectionProvider().getSelection();
                                    if(selection instanceof ITextSelection){
                                       try {
                                          IJavaElement method = compUnit.getElementAt(((ITextSelection) selection).getOffset());
                                          if(method != null && method.getElementType() == IJavaElement.METHOD){
                                             editorSelection.setSelectedMethod((IMethod) method);
                                          }
                                       }
                                       catch (JavaModelException e) {
                                          LogUtil.getLogger().logError(e);
                                       }   
                                    }
                                 }
                                 else{
                                    editorSelection.addOpenFile((IFile) res);
                                 }
                              }
                           }
                        }
                        else if(editor instanceof KeYEditor){
                           IEditorInput editorInput = editor.getEditorInput();
                           if(editorInput != null && editorInput instanceof IFileEditorInput){
                              IFile file = ((IFileEditorInput) editorInput).getFile();
                              if(file != null && file.exists() && project.equals(file.getProject()) 
                                    && KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(file.getFileExtension())
                                    && KeYResourcesUtil.isInProofFolder(file)){
                                 if(editor.equals(activeEditor) && editorSelection.getActiveFile() == null){
                                    editorSelection.setActiveFile(file);
                                 }
                                 else{
                                    editorSelection.addOpenFile(file);
                                 }
                              }
                           }
                        }
                     }
                  }
               }
            }
         }
      });
      
      return editorSelection;
   }
}
