package de.uka.ilkd.key.gui;

import java.awt.Component;
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
import java.util.LinkedList;
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

import de.uka.ilkd.key.settings.ProofSettings;
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

   private static abstract class SendFeedbackItem<C extends Component> {
      final String fileName;
      final C component;

      SendFeedbackItem(String fileName, C component) {
         this.fileName = fileName;
         this.component = component;
      }

      abstract byte[] getData();
   }

   private LinkedList<SendFeedbackItem<JCheckBox>> checkBoxes = new LinkedList<>();
   private final Window parent;

   SendFeedbackItem<JTextArea> bugDescription = new SendFeedbackItem<JTextArea>(
         "bugDescription.txt", new JTextArea(20, 50)) {
      @Override
      byte[] getData() {
         return component.getText().getBytes();
      }
   };

   public SendFeedbackAction(Window parent) {
      super("Send Feedback");
      this.parent = parent;

      checkBoxes.add(new SendFeedbackItem<JCheckBox>("loadedProblem.key",
            new JCheckBox("Send Loaded Problem", true)) {
         @Override
         byte[] getData() {
            if (component.isSelected()) {
               File mostRecentFile = new File(MainWindow.getInstance()
                     .getRecentFiles().getMostRecent().getAbsolutePath());
               try {
                  return Files.readAllBytes(mostRecentFile.toPath());
               }
               catch (IOException e) {
                  return ("Cannot read most recent file:\n" + e.getMessage())
                        .getBytes();
               }
            }
            else {
               return null;
            }
         }
      });

      checkBoxes.add(new SendFeedbackItem<JCheckBox>("keyVersion.txt",
            new JCheckBox("Send KeY Version", true)) {
         @Override
         byte[] getData() {
            if (component.isSelected()) {
               return KeYConstants.VERSION.getBytes();
            }
            else {
               return null;
            }
         }
      });

      checkBoxes.add(new SendFeedbackItem<JCheckBox>("systemProperties.txt",
            new JCheckBox("Send System Properties", true)) {
         @Override
         byte[] getData() {
            if (component.isSelected()) {
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
      });

      checkBoxes.add(new SendFeedbackItem<JCheckBox>("openGoal.txt",
            new JCheckBox("Send Open Goal", true)) {
         @Override
         byte[] getData() {
            if (component.isSelected()) {
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
      });

      checkBoxes.add(new SendFeedbackItem<JCheckBox>("openProof.proof",
            new JCheckBox("Send Open Proof", true)) {
         @Override
         byte[] getData() {
            if (component.isSelected()) {
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
      });

      checkBoxes.add(new SendFeedbackItem<JCheckBox>("keySettings.txt",
            new JCheckBox("Send KeY Settings", true)) {
         @Override
         byte[] getData() {
            if (component.isSelected()) {
               try {
                  return ProofSettings.DEFAULT_SETTINGS.settingsToString()
                        .getBytes();
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
      });
   }

   SendFeedbackAction(final Window parent, final Throwable exception) {
      this(parent);

      final JCheckBox sendErrorMessageCheckBox = new JCheckBox(
            "Send Error Message", true);
      SendFeedbackItem<JCheckBox> errorMessageFeedbackitem = new SendFeedbackItem<JCheckBox>(
            "errorMessage.txt", sendErrorMessageCheckBox) {
         @Override
         byte[] getData() {
            if (component.isSelected()) {
               return exception.getMessage().getBytes();
            }
            else {
               return null;
            }
         }
      };

      final JCheckBox sendStackTraceCheckBox = new JCheckBox("Send Stacktrace",
            true);
      SendFeedbackItem<JCheckBox> stackTraceFeedbackItem = new SendFeedbackItem<JCheckBox>(
            "stacktrace.txt", sendStackTraceCheckBox) {
         @Override
         byte[] getData() {
            if (component.isEnabled() && component.isSelected()) {
               return serializeStackTrace(exception).getBytes();
            }
            else {
               return null;
            }
         }
      };

      sendErrorMessageCheckBox.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent e) {
            sendStackTraceCheckBox.setEnabled(sendErrorMessageCheckBox
                  .isSelected());
         }
      });

      checkBoxes.addFirst(errorMessageFeedbackitem);
      checkBoxes.addFirst(stackTraceFeedbackItem);

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
      for (SendFeedbackItem<JCheckBox> i : checkBoxes) {
         right.add(i.component);
      }

      bugDescription.component.setLineWrap(true);
      bugDescription.component.setBorder(new TitledBorder(
            "Message to Developers"));
      JScrollPane left = new JScrollPane(bugDescription.component);
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
               for (SendFeedbackItem<JCheckBox> i : checkBoxes) {
                  byte[] data = i.getData();
                  if (data != null) {
                     stream.putNextEntry(new ZipEntry(i.fileName));
                     stream.write(data);
                     stream.closeEntry();
                  }
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
