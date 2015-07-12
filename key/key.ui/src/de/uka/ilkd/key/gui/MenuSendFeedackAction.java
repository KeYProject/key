package de.uka.ilkd.key.gui;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.actions.MainWindowAction;

public class MenuSendFeedackAction extends MainWindowAction {
   
   protected MenuSendFeedackAction(MainWindow mainWindow) {
      super(mainWindow);
   }

   /**
    * Re-using {@link SendFeedbackAction} from {@link ExceptionDialog} for this.
    */
   private SendFeedbackAction action = new SendFeedbackAction(mainWindow);

   @Override
   public void actionPerformed(ActionEvent arg0) {
      action.actionPerformed(arg0);
   }
}
