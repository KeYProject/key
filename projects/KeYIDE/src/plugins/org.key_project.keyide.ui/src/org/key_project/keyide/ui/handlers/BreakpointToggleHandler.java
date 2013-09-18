package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.keyide.ui.editor.KeYEditor;

public class BreakpointToggleHandler extends AbstractHandler {
   
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      
      
      Command command = event.getCommand();
      boolean oldValue = HandlerUtil.toggleCommandState(command);
      boolean newValue = !oldValue;
      // use the old value and perform the operation
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      if (editorPart != null && editorPart instanceof KeYEditor) {
         KeYEditor editor = (KeYEditor)editorPart;
         editor.setBreakpointsActivated(newValue);
      }
      return null;
   }

}
