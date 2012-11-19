package org.key_project.keyide.ui.contextmenu.selectproof;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.internal.ui.javaeditor.EditorUtility;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewActionDelegate;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.PlatformUI;
import org.key_project.key4eclipse.starter.core.job.AbstractKeYMainWindowJob;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.speclang.FunctionalOperationContract;


public class SelectProof implements IViewActionDelegate{

   
      @Override
      public void run(IAction action) {
         
         try {
            doExecute(action);
         }
         catch (Exception e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }

      }
      
      @SuppressWarnings("restriction")
      public void doExecute(IAction action) throws Exception{         
         ISelection selection = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getSelectionService().getSelection();
         if (selection instanceof IStructuredSelection) {
            Object[] elements = SWTUtil.toArray(selection);
            for (Object element : elements) {
                if (element instanceof IMethod) {
                   IMethod method = (IMethod)element;
                   KeYUtil.startProofAsync(method);
                }
            }
        }
         else if (selection instanceof ITextSelection) {            
            ITextSelection textSelection = (ITextSelection)selection;
            IEditorPart editor = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
            ICompilationUnit root = (ICompilationUnit) EditorUtility.getEditorInputJavaElement(editor, false);
            int offset = textSelection.getOffset();
            if (editor instanceof JavaEditor) {
                JavaEditor javaEditor = (JavaEditor)editor;
                IJavaElement element = root.getElementAt(offset);
                System.out.println(element.getClass().toString());
                if (element instanceof IMethod) {
                   IMethod method = (IMethod)element;
                   KeYUtil.startProofAsync(method);
                }
            }
        } 
         
         
         // TODO: Open contract selection
         final IMethod method; // Siehe obne
         new AbstractKeYMainWindowJob("Test") { // A Job which does something with KeY
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               try {
                  
                  // See MainLaunchConfigurationComposite.browseContract()
                  FunctionalOperationContract contract; // 
                  
                  // Pass contract and initConfig to opened editor IEditorInput
                  
                  monitor.beginTask("Test", 10);// IProgressMonitor.UNKNOWN
                  for (int i = 0; i < 10; i++) {
                     SWTUtil.checkCanceled(monitor);
                     monitor.subTask("This is " + i);
                     monitor.worked(1);
                  }
                  monitor.done();
                  return Status.OK_STATUS;
               }
               catch (OperationCanceledException e) {
                  return Status.CANCEL_STATUS;
               }
            }
            
         }.schedule();
         
         // TODO: Only if user selected a contract
         // TODO: Ask the user first, similar to ConfigurationObjectDiagramEditor#openEditor()
         WorkbenchUtil.openPerspective("org.key_project.keyide.product.perspectives");
         
         
         


      }
      
      @Override
      public void selectionChanged(IAction action, ISelection selection) {
         // TODO Auto-generated method stub
         
      }

      @Override
      public void init(IViewPart view) {
         // TODO Auto-generated method stub
         
      }

   }