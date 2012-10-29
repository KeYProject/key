package org.key_project.sed.ui.visualization.util;

import org.eclipse.gef.ui.actions.UpdateAction;
import org.eclipse.jface.action.IAction;
import org.key_project.util.eclipse.view.editorInView.GlobalEnablementWrapperAction;

public class GraphitiGlobalEnablementWrapperAction extends GlobalEnablementWrapperAction implements UpdateAction {

   public GraphitiGlobalEnablementWrapperAction(IAction action) {
      super(action);
   }

   @Override
   public void update() {
      if (getAction() instanceof UpdateAction) {
         ((UpdateAction)getAction()).update();
      }
   }
}
