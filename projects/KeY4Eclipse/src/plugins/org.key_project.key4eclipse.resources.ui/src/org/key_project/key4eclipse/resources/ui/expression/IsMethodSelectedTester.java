package org.key_project.key4eclipse.resources.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.ITextEditor;

public class IsMethodSelectedTester extends PropertyTester {

   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      if(receiver instanceof ITextSelection){
         IWorkbenchWindow activeWorkbenchWindow = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
         if(activeWorkbenchWindow != null){
            IWorkbenchPage activeWorkbenchPage = activeWorkbenchWindow.getActivePage();
            if(activeWorkbenchPage != null){
               IEditorPart activeEditor = activeWorkbenchPage.getActiveEditor();
               if(activeEditor != null && activeEditor instanceof ITextEditor){
                  IEditorInput editorInput = activeEditor.getEditorInput();
                  if(editorInput != null){
                     IJavaElement javaElement = JavaUI.getEditorInputJavaElement(activeEditor.getEditorInput());
                     if(javaElement != null && javaElement instanceof ICompilationUnit){
                        try {
                           ICompilationUnit compUnit = (ICompilationUnit) javaElement;
                           ITextEditor textEditor = (ITextEditor) activeEditor;
                           ISelection selection = textEditor.getSelectionProvider().getSelection();
                           if(selection instanceof ITextSelection){
                              IJavaElement selectedElement = compUnit.getElementAt(((ITextSelection) selection).getOffset());
                              if(selectedElement != null && IJavaElement.METHOD == selectedElement.getElementType()){
                                 return true;
                              }
                           }
                        }
                        catch (JavaModelException e) {
                           return false;
                        }
                     }
                  }
               }
            }
         }
      }
      return false;
   }

}
