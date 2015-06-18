package org.key_project.sed.key.evaluation.preference.page;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.sed.key.evaluation.io.SendThread;
import org.key_project.sed.key.evaluation.model.util.ServerSettings;
import org.key_project.sed.key.evaluation.util.LogUtil;

/**
 * Read-only {@link PreferencePage} which shows the SED evaluation server and allows to ping it.
 * @author Martin Hentschel
 */
public class SEDEvaluationServerPreferencePage extends PreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor.
    */
   public SEDEvaluationServerPreferencePage() {
      noDefaultAndApplyButton();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createContents(Composite parent) {
      Composite composite = new Composite(parent, SWT.NONE);
      composite.setLayout(new GridLayout(2, false));
      Label serverLabel = new Label(composite, SWT.NONE);
      serverLabel.setText("Server");
      Text serverText = new Text(composite, SWT.BORDER | SWT.READ_ONLY);
      serverText.setText(ServerSettings.HOST + ":" + ServerSettings.PORT);
      serverText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      
      new Label(composite, SWT.NONE);
      Button button = new Button(composite, SWT.PUSH);
      button.setText("Ping Server");
      button.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      button.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            pingServer();
         }
      });
      return composite;
   }

   /**
    * Pings the server and shows the result to the user in an opened dialog.
    */
   public void pingServer() {
      try {
         long time = SendThread.ping();
         MessageDialog.openInformation(getShell(), "Ping", "Server answered within " + time + " milli seconds.");
      }
      catch (Exception e) {
         LogUtil.getLogger().openErrorDialog(getShell(), e);
      }
   }
}
