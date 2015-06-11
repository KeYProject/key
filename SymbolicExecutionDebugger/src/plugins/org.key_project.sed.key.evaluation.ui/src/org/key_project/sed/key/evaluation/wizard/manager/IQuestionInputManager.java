package org.key_project.sed.key.evaluation.wizard.manager;

import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.services.IDisposable;

public interface IQuestionInputManager extends IDisposable {
   public boolean isEnabled();
   
   public void setEnabled(boolean enabled);

   public Control getFocusControl();
}
