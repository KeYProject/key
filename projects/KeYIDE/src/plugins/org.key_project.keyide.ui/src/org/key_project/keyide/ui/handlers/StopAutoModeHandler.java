package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandlerListener;
import org.key_project.keyide.ui.util.KeYToUIUtil;
import org.key_project.keyide.ui.views.Outline;

import de.uka.ilkd.key.gui.prooftree.GUIProofTreeModel;
import de.uka.ilkd.key.proof.Proof;

public class StopAutoModeHandler extends AbstractSaveExecutionHandler {



   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      
      //nur zu testzwecken
      Proof proof = KeYToUIUtil.getProof();
      
//      proof.addProofTreeListener(listener)
//      
      Outline.viewer.setInput(new GUIProofTreeModel(proof).getRoot());
      /*KeYToUIUtil.getUi().stopAutoMode();
       KeYToUIUtil.getUi().notifyAutomodeStopped();
       */
      return null;
   }

}
