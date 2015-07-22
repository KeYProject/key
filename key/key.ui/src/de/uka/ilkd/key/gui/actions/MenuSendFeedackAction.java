package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;

public class MenuSendFeedackAction extends MainWindowAction {
   
   public MenuSendFeedackAction(MainWindow mainWindow) {
      super(mainWindow);
      setName("Send Feedback");
   }

   /**
    * Re-using {@link SendFeedbackAction} from {@link ExceptionDialog} for this.
    */
   private final SendFeedbackAction action = new SendFeedbackAction(mainWindow);

   @Override
   public void actionPerformed(ActionEvent arg0) {
      action.actionPerformed(arg0);
   }
}
