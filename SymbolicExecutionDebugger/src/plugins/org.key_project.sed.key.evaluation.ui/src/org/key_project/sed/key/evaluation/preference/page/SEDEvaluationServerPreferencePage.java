package org.key_project.sed.key.evaluation.preference.page;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.sed.key.evaluation.io.SendThread;
import org.key_project.sed.key.evaluation.model.util.ServerPreferences;
import org.key_project.sed.key.evaluation.util.LogUtil;

/**
 * Read-only {@link PreferencePage} which shows the SED evaluation server and allows to ping it.
 * @author Martin Hentschel
 */
public class SEDEvaluationServerPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   private StringFieldEditor hostEditor;
   
   private IntegerFieldEditor portEditor;
   
   /**
    * Constructor.
    */
   public SEDEvaluationServerPreferencePage() {
      super(GRID);
   }

   @Override
   public void init(IWorkbench workbench) {
      setPreferenceStore(ServerPreferences.getStore());
   }

   @Override
   protected void createFieldEditors() {
      hostEditor = new StringFieldEditor(ServerPreferences.HOST, "Host", getFieldEditorParent());
      portEditor = new IntegerFieldEditor(ServerPreferences.PORT, "Port", getFieldEditorParent());
      portEditor.setValidRange(0, Integer.MAX_VALUE);
      addField(hostEditor);
      addField(portEditor);

      Button button = new Button(getFieldEditorParent(), SWT.PUSH);
      GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
      gridData.horizontalSpan = 2;
      button.setLayoutData(gridData);
      button.setText("Ping Server");
      button.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            pingServer();
         }
      });
   }
   
   /**
    * Pings the server and shows the result to the user in an opened dialog.
    */
   public void pingServer() {
      try {
         long time = SendThread.ping(hostEditor.getStringValue(), portEditor.getIntValue());
         MessageDialog.openInformation(getShell(), "Ping", "Server answered within " + time + " milli seconds.");
      }
      catch (Exception e) {
         LogUtil.getLogger().openErrorDialog(getShell(), e);
      }
   }
}
