//package org.key_project.key4eclipse.resources.util;
//
//import org.eclipse.core.resources.IFile;
//import org.eclipse.jdt.core.IJavaElement;
//import org.eclipse.jdt.ui.JavaUI;
//import org.eclipse.jface.text.ITextSelection;
//import org.eclipse.jface.viewers.ISelection;
//import org.eclipse.swt.widgets.Display;
//import org.eclipse.ui.IEditorInput;
//import org.eclipse.ui.IEditorPart;
//import org.eclipse.ui.IEditorReference;
//import org.eclipse.ui.IFileEditorInput;
//import org.eclipse.ui.IWorkbenchPage;
//import org.eclipse.ui.PlatformUI;
//import org.eclipse.ui.texteditor.ITextEditor;
//
//// TOOD: Do not understand this class. May remove it?
//public class EditorSelector {
//   
//   private final EditorSelection editorSelection = new EditorSelection();
//   
//   public EditorSelector(){
////      Display.getDefault().syncExec(new Runnable() {
////         @Override
////         public void run() {
////            IWorkbenchPage activePage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
////            
////            IEditorPart activeEditorPart = activePage.getActiveEditor();
////            if(isJavaFile(activeEditorPart)){
////               editorSelection.setActiveFile(((IFileEditorInput) activeEditorPart.getEditorInput()).getFile());
////               if(isJavaFile(activeEditorPart) && activeEditorPart instanceof ITextEditor){
////                  ITextEditor textEditor = (ITextEditor) activeEditorPart;
////                  ISelection selection = textEditor.getSelectionProvider().getSelection();
////                  if(selection instanceof ITextSelection){
////                     editorSelection.setActiveSelection((ITextSelection) selection);
////                  }
////               }
////            }
////            else if(isKeYFile(activeEditorPart)){
////               editorSelection.setActiveFile(((IFileEditorInput) activeEditorPart.getEditorInput()).getFile());
////            }
////            IEditorReference[] editorRefs = activePage.getEditorReferences();
////            for(IEditorReference editorRef : editorRefs){
////               IEditorPart editorPart = editorRef.getEditor(true);
////               if(editorPart != null && isJavaFile(editorPart) || isKeYFile(editorPart)){
////                  IFile file = ((IFileEditorInput) editorPart.getEditorInput()).getFile();
////                  if(file != null && !file.equals(editorSelection.getActiveFile())){
////                     editorSelection.addOpenFile(file);
////                  }
////               }
////            }
////         }
////         
////         private boolean isJavaFile(IEditorPart editorPart){
////            if(editorPart != null){
////               IEditorInput editorInput = editorPart.getEditorInput();
////               if(editorInput instanceof IFileEditorInput){
////                  IJavaElement javaElement = JavaUI.getEditorInputJavaElement(editorInput);
////                  if(javaElement != null){
////                     return true;
////                  }
////               }
////            }
////            return false;
////         }
////         
////         public boolean isKeYFile(IEditorPart editorPart){
////            if(editorPart != null){
////               IEditorInput editorInput = editorPart.getEditorInput();
////               if(editorInput instanceof IFileEditorInput){
////                  IFileEditorInput fileEditorInput = (IFileEditorInput) editorInput;
////                  IFile file = fileEditorInput.getFile();
////                  if(KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(file.getFileExtension()) || KeYResourcesUtil.META_FILE_EXTENSION.equals(file.getFileExtension())){
////                     return true;
////                  }
////               }
////            }
////            return false;
////         }
////      });
//   }
//   
//   public EditorSelection getEditorSelection(){
//      return editorSelection;
//   }
//
//
//}
