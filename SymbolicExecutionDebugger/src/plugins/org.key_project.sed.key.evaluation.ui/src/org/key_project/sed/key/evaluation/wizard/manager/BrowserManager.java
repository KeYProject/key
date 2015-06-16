package org.key_project.sed.key.evaluation.wizard.manager;

import java.io.IOException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.swt.SWT;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.BrowserQuestion;

public class BrowserManager extends AbstractQuestionInputManager {
   private Browser browser;
   
   public BrowserManager(FormToolkit toolkit, 
                         Composite parent, 
                         BrowserQuestion question) {
      browser = createBrowser(toolkit, parent, question.getUrl());
   }

   @Override
   public void dispose() {
      // Nothing special to do
   }
   
   public static Browser createBrowser(FormToolkit toolkit, Composite parent, URL url) {
      Browser browser = new Browser(parent, SWT.BORDER);
      toolkit.adapt(browser);
      browser.setLayoutData(new GridData(GridData.FILL_BOTH));
      browser.setMenu(new MenuManager().createContextMenu(browser)); // Disable context menu
      try {
         if (url != null) {
            URL fileUrl = FileLocator.toFileURL(url); 
            browser.setUrl(fileUrl.toString());
         }
      }
      catch (IOException e) {
         browser.setText(e.getMessage());
      }
      return browser;
   }

   @Override
   protected void enableControls(boolean enabled) {
      browser.setEnabled(enabled);
   }

   @Override
   public Control getFocusControl() {
      return browser;
   }
}
