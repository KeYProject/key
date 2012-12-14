package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.util.KeYIDEUtil;

import de.uka.ilkd.key.proof.Proof;

/**
 * An {@link AbstractSaveExecutionHandler} for the Start Proof command.
 * Safely selects a contract and initialize a {@link Proof} for the current selection.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
@SuppressWarnings({ "restriction" })
public class StartProofHandler extends AbstractSaveExecutionHandler {

   /** 
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(final ExecutionEvent event) throws Exception {
       ISelection selection = HandlerUtil.getCurrentSelection(event);
       if (selection instanceof IStructuredSelection) {
           Object[] elements = ((IStructuredSelection)selection).toArray();
           for (Object element : elements) {
               if (element instanceof IMethod) {
                   KeYIDEUtil.openProofEditor((IMethod)element);
                   KeYIDEUtil.switchPerspective();
               }
           }
       }
       else if (selection instanceof ITextSelection) {
           ITextSelection textSelection = (ITextSelection)selection;
           IEditorPart editor = HandlerUtil.getActiveEditor(event);
           if (editor instanceof JavaEditor) {
               JavaEditor javaEditor = (JavaEditor)editor;
               IJavaElement element = SelectionConverter.resolveEnclosingElement(javaEditor, textSelection);
               if (element instanceof IMethod) {
                   KeYIDEUtil.openProofEditor((IMethod)element);
                   KeYIDEUtil.switchPerspective();
               }
           }
       }
       return null;
   }   
}
 