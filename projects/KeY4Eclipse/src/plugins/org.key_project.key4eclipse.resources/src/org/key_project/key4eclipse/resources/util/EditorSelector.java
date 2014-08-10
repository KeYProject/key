package org.key_project.key4eclipse.resources.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.ITextEditor;

public class EditorSelector {
   
   private final EditorSelection editorSelection = new EditorSelection();
   
   public EditorSelector(){
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            IWorkbenchPage activePage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
            
            IEditorPart activeEditorPart = activePage.getActiveEditor();
            if(isJavaEditor(activeEditorPart)){
               editorSelection.setActiveEditor((ITextEditor) activeEditorPart);
               
               ITextSelection selection = (ITextSelection) ((ITextEditor) activeEditorPart).getSelectionProvider().getSelection();
               editorSelection.setActiveSelection(selection);
            }
            
            IEditorReference[] editorRefs = activePage.getEditorReferences();
            for(IEditorReference editorRef : editorRefs){
               IEditorPart editorPart = editorRef.getEditor(true);
               if(editorPart != null && isJavaEditor(editorPart) && !editorPart.equals(activeEditorPart)){
                  editorSelection.addOpenEditor((ITextEditor) editorPart);
               }
            }
         }
      });
   }
   

   private static boolean isJavaEditor(IEditorPart editorPart){
      if(editorPart != null && editorPart instanceof ITextEditor){
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
   
   
   public EditorSelection getEditorSelection(){
      return editorSelection;
   }
}
