package de.uka.ilkd.key.gui;

import java.awt.Container;
import java.awt.Dialog;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import javax.swing.AbstractAction;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.util.KeYConstants;

/**
 * {@link AbstractAction} used by {@link ExceptionDialog} in KeY report error
 * button was pressed.
 * 
 * @author Kai Wallisch
 *
 */
public class SendFeedbackAction extends AbstractAction {

   private static String serializeStackTrace(Throwable t) {
      String stackTrace = "";
      for (StackTraceElement e : t.getStackTrace()) {
         stackTrace += e.toString() + "\n";
      }
      return stackTrace;
   }

   // suggested e-Mail address that bug reports shall be sent to
   private final String BUG_REPORT_RECIPIENT = null;

   private static abstract class BugMetaDataObject {
      final String fileName;

      BugMetaDataObject(String fileName) {
         this.fileName = fileName;
      }

      abstract byte[] getData();

   }

   private final JCheckBox sendErrorMessage = new JCheckBox(
         "Send Error Message", true);
   private static final String ERROR_MESSAGE_FILENAME = "errorMessage.txt";
   private final JCheckBox sendStacktrace = new JCheckBox("Send Stacktrace",
         true);
   private static final String STACKTRACE_FILENAME = "stacktrace.txt";
   private final JCheckBox sendLoadedProblem = new JCheckBox(
         "Send Loaded Problem", true);
   private static final String LOADED_PROBLEM_FILENAME = "loadedProblem.key";
   private final JCheckBox sendKeYVersion = new JCheckBox("Send KeY Version",
         true);
   private static final String KEY_VERSION_FILENAME = "keyVersion.txt";
   private final JCheckBox sendKeYSettings = new JCheckBox("Send KeY Settings",
         true);
   private static final String KEY_SETTINGS_FILENAME = "keySettings.txt";
   private final JCheckBox sendSystemProperties = new JCheckBox(
         "Send System Properties", true);
   private static final String SYSTEM_PROPERTIES_FILENAME = "systemProperties.txt";
   private final JTextArea bugDescription = new JTextArea(20, 50);
   private static final String BUG_DESCRIPTION_FILENAME = "bugDescription.txt";
   private static final String OPEN_GOAL_FILENAME = "openGoal.txt";
   private final JCheckBox sendOpenGoal = new JCheckBox("Send Open Goal", true);
   private static final String OPEN_PROOF_FILENAME = "openProof.proof";
   private final JCheckBox sendOpenProof = new JCheckBox("Send Open Proof",
         true);

   private final BugMetaDataObject metaDataObject[];
   private final Window parent;

   SendFeedbackAction(final Window parent, final Throwable exception) {
      super("Send Feedback");
      this.parent = parent;

      metaDataObject = new BugMetaDataObject[] {
            new BugMetaDataObject(ERROR_MESSAGE_FILENAME) {
               @Override
               byte[] getData() {
                  if (sendErrorMessage.isSelected()) {
                     return exception.getMessage().getBytes();
                  }
                  else {
                     return null;
                  }
               }

            }, new BugMetaDataObject(STACKTRACE_FILENAME) {
               @Override
               byte[] getData() {
                  if (sendStacktrace.isEnabled() && sendStacktrace.isSelected()) {
                     return serializeStackTrace(exception).getBytes();
                  }
                  else {
                     return null;
                  }
               }
            }, new BugMetaDataObject(LOADED_PROBLEM_FILENAME) {
               @Override
               byte[] getData() {
                  if (sendLoadedProblem.isSelected()) {
                     File mostRecentFile = new File(MainWindow.getInstance()
                           .getRecentFiles().getMostRecent().getAbsolutePath());
                     try {
                        return Files.readAllBytes(mostRecentFile.toPath());
                     }
                     catch (IOException e) {
                        return ("Cannot read most recent file:\n" + e
                              .getMessage()).getBytes();
                     }
                  }
                  else {
                     return null;
                  }
               }
            }, new BugMetaDataObject(KEY_VERSION_FILENAME) {
               @Override
               byte[] getData() {
                  if (sendKeYVersion.isSelected()) {
                     return KeYConstants.VERSION.getBytes();
                  }
                  else {
                     return null;
                  }
               }
            }, new BugMetaDataObject(SYSTEM_PROPERTIES_FILENAME) {
               @Override
               byte[] getData() {
                  if (sendSystemProperties.isSelected()) {
                     StringWriter sw = new StringWriter();
                     PrintWriter pw = new PrintWriter(sw);
                     System.getProperties().list(pw);
                     String propsAsString = sw.getBuffer().toString();
                     pw.close();
                     return propsAsString.getBytes();
                  }
                  else {
                     return null;
                  }
               }
            }, new BugMetaDataObject(BUG_DESCRIPTION_FILENAME) {
               @Override
               byte[] getData() {
                  return bugDescription.getText().getBytes();
               }
            }, new BugMetaDataObject(OPEN_GOAL_FILENAME) {
               @Override
               byte[] getData() {
                  if (sendOpenGoal.isSelected()) {
                     try {
                        return MainWindow.getInstance().getMediator()
                              .getSelectedGoal().toString().getBytes();
                     }
                     catch (Exception e) {
                        return ("Cannot read open goal: "
                              + e.getClass().getSimpleName() + "\n" + serializeStackTrace(e))
                              .getBytes();
                     }
                  }
                  else {
                     return null;
                  }
               }
            }, new BugMetaDataObject(OPEN_PROOF_FILENAME) {
               @Override
               byte[] getData() {
                  if (sendOpenProof.isSelected()) {
                     try {
                        return MainWindow.getInstance().getMediator()
                              .getSelectedProof().toString().getBytes();
                     }
                     catch (Exception e) {
                        return ("Cannot read open proof: "
                              + e.getClass().getSimpleName() + "\n" + serializeStackTrace(e))
                              .getBytes();
                     }
                  }
                  else {
                     return null;
                  }
               }
            } };
   }

   @Override
   public void actionPerformed(ActionEvent arg0) {
      final JDialog dialog = new JDialog(parent,
            "Report an Error to KeY Developers",
            Dialog.ModalityType.DOCUMENT_MODAL);
      dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
      dialog.setBounds(parent.getBounds());

      JPanel right = new JPanel();
      right.setLayout(new BoxLayout(right, BoxLayout.Y_AXIS));
      right.add(sendErrorMessage);
      right.add(sendStacktrace);
      sendErrorMessage.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent e) {
            sendStacktrace.setEnabled(sendErrorMessage.isSelected());
         }
      });
      right.add(sendLoadedProblem);
      right.add(sendKeYVersion);
      right.add(sendKeYSettings);
      right.add(sendSystemProperties);
      right.add(sendOpenGoal);
      right.add(sendOpenProof);

      bugDescription.setLineWrap(true);
      bugDescription.setBorder(new TitledBorder("Message to Developers"));
      JScrollPane left = new JScrollPane(bugDescription);
      left.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
      left.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

      JPanel topPanel = new JPanel();
      topPanel.setLayout(new BoxLayout(topPanel, BoxLayout.X_AXIS));
      topPanel.add(left);
      topPanel.add(right);

      JPanel buttonPanel = new JPanel();
      buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));

      JButton sendFeedbackReportButton = new JButton("Send Feedback");
      sendFeedbackReportButton.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent arg0) {
            int confirmed = JOptionPane
                  .showConfirmDialog(
                        parent,
                        "A zip archive containing the selected metadata will be created.\n"
                              + "Please send an e-Mail containing this zip file as attachment to:\n"
                              + BUG_REPORT_RECIPIENT, "Send Bug Report",
                        JOptionPane.OK_CANCEL_OPTION);
            if (confirmed == JOptionPane.OK_OPTION) {
               KeYFileChooser fileChooser = KeYFileChooser
                     .getFileChooser("Save Zip File");
               File zipFile = new File(fileChooser.getCurrentDirectory(),
                     "BugReport.zip");
               boolean fileSelectionConfirmed = fileChooser.showSaveDialog(
                     parent, zipFile);
               if (fileSelectionConfirmed) {
                  zipFile = fileChooser.getSelectedFile();
                  try {
                     saveMetaDataToFile(zipFile);
                  }
                  catch (IOException e) {
                     JOptionPane.showMessageDialog(parent, e.getMessage());
                  }
                  dialog.dispose();
               }
            }
         }

         private void saveMetaDataToFile(File zipFile) throws IOException {

            ZipOutputStream stream = null;
            try {
               stream = new ZipOutputStream(new BufferedOutputStream(
                     new FileOutputStream(zipFile)));
               for (BugMetaDataObject o : metaDataObject) {
                  stream.putNextEntry(new ZipEntry(o.fileName));
                  stream.write(o.getData());
                  stream.closeEntry();
               }
            }
            catch (FileNotFoundException e) {
               JOptionPane.showMessageDialog(parent, e.getMessage());
            }
            finally {
               if (stream != null) {
                  stream.close();
               }
            }
         }
      });

      JButton cancelButton = new JButton("Cancel");
      cancelButton.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent e) {
            dialog.dispose();
         }
      });

      buttonPanel.add(sendFeedbackReportButton);
      buttonPanel.add(cancelButton);

      Container container = dialog.getContentPane();
      container.setLayout(new BoxLayout(container, BoxLayout.Y_AXIS));
      container.add(topPanel);
      container.add(buttonPanel);

      dialog.pack();
      dialog.setVisible(true);
   }
}
