package org.key_project.key4eclipse.resources.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;

public class EditorSelector {
   
   private final EditorSelection editorSelection = new EditorSelection();
   
   public EditorSelector(){
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            IWorkbenchPage activePage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
            
            IEditorPart activeEditorPart = activePage.getActiveEditor();
            if(isJavaFile(activeEditorPart)){
               editorSelection.setActiveFile(((IFileEditorInput) activeEditorPart.getEditorInput()).getFile());
               if(isJavaEditor(activeEditorPart)){
                  JavaEditor javaEditor = (JavaEditor) activeEditorPart;
                  ISelection selection = javaEditor.getSelectionProvider().getSelection();
                  if(selection instanceof ITextSelection){
                     editorSelection.setActiveSelection((ITextSelection) javaEditor.getSelectionProvider().getSelection());
                  }
               }
            }
            else if(isKeYFile(activeEditorPart)){
               editorSelection.setActiveFile(((IFileEditorInput) activeEditorPart.getEditorInput()).getFile());
            }
            
            IEditorReference[] editorRefs = activePage.getEditorReferences();
            for(IEditorReference editorRef : editorRefs){
               IEditorPart editorPart = editorRef.getEditor(true);
               if(editorPart != null && isJavaFile(editorPart) || isKeYFile(editorPart)){
                  IFile file = ((IFileEditorInput) editorPart.getEditorInput()).getFile();
                  if(file != null && !file.equals(editorSelection.getActiveFile())){
                     editorSelection.addOpenFile(file);
                  }
               }
            }
         }
         
         private boolean isJavaFile(IEditorPart editorPart){
            if(editorPart != null){
               IEditorInput editorInput = editorPart.getEditorInput();
               if(editorInput instanceof IFileEditorInput){
                  IFileEditorInput fileEditorInput = (IFileEditorInput) editorInput;
                  IFile file = fileEditorInput.getFile();
                  IJavaElement javaElement = JavaCore.create(file);
                  if(javaElement != null){
                     return true;
                  }
                  
               }
            }
            return false;
         }

         private boolean isJavaEditor(IEditorPart editorPart) {
            if(editorPart != null && editorPart instanceof JavaEditor){
               return true;
            }
            return false;
         }
         
         public boolean isKeYFile(IEditorPart editorPart){
            if(editorPart != null){
               IEditorInput editorInput = editorPart.getEditorInput();
               if(editorInput instanceof IFileEditorInput){
                  IFileEditorInput fileEditorInput = (IFileEditorInput) editorInput;
                  IFile file = fileEditorInput.getFile();
                  if("proof".equals(file.getFileExtension()) || "proofmeta".equals(file.getFileExtension())){
                     return true;
                  }
               }
            }
            return false;
         }
      });
   }
   
      
   
   
   
   public EditorSelection getEditorSelection(){
      return editorSelection;
   }


}
