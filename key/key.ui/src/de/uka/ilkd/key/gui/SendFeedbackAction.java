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

   // dialog that opens in case user wished to send feedback
   private final JDialog dialog;

   private static abstract class SendFeedbackItem {
      final String fileName;
      final JCheckBox checkBox;

      SendFeedbackItem(String fileName, JCheckBox checkBox) {
         this.fileName = fileName;
         this.checkBox = checkBox;
      }

      abstract byte[] computeData() throws Exception;

      void addZipEntry(ZipOutputStream stream) throws IOException {
         if (checkBox.isSelected() && checkBox.isEnabled()) {
            byte[] data;
            String zipEntryFileName = fileName;
            try {
               data = computeData();
            }
            catch (Exception e) {
               zipEntryFileName += ".exception";
               data = (e.getClass().getSimpleName()
                     + " occured while trying to read data.\n" + e.getMessage()
                     + "\n" + serializeStackTrace(e)).getBytes();
            }
            stream.putNextEntry(new ZipEntry(zipEntryFileName));
            stream.write(data);
            stream.closeEntry();
         }
      }
   }

   // checkboxes specifing which data will be contained in feedback
   private LinkedList<SendFeedbackItem> checkBoxes = new LinkedList<>();

   public SendFeedbackAction(final Window parent) {
      super("Send Feedback");

      checkBoxes.add(new SendFeedbackItem("loadedProblem.key", new JCheckBox(
            "Send Loaded Problem", true)) {
         @Override
         byte[] computeData() throws IOException {
            File mostRecentFile = new File(MainWindow.getInstance()
                  .getRecentFiles().getMostRecent().getAbsolutePath());
            return Files.readAllBytes(mostRecentFile.toPath());
         }
      });

      checkBoxes.add(new SendFeedbackItem("keyVersion.txt", new JCheckBox(
            "Send KeY Version", true)) {
         @Override
         byte[] computeData() {
            return KeYConstants.VERSION.getBytes();
         }
      });

      checkBoxes.add(new SendFeedbackItem("systemProperties.txt",
            new JCheckBox("Send System Properties", true)) {
         @Override
         byte[] computeData() {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            System.getProperties().list(pw);
            String propsAsString = sw.getBuffer().toString();
            pw.close();
            return propsAsString.getBytes();
         }
      });

      checkBoxes.add(new SendFeedbackItem("openGoal.txt", new JCheckBox(
            "Send Open Goal", true)) {
         @Override
         byte[] computeData() {
            return MainWindow.getInstance().getMediator().getSelectedGoal()
                  .toString().getBytes();
         }
      });

      checkBoxes.add(new SendFeedbackItem("openProof.proof", new JCheckBox(
            "Send Open Proof", true)) {
         @Override
         byte[] computeData() {
            return MainWindow.getInstance().getMediator().getSelectedProof()
                  .toString().getBytes();
         }
      });

      checkBoxes.add(new SendFeedbackItem("keySettings.txt", new JCheckBox(
            "Send KeY Settings", true)) {
         @Override
         byte[] computeData() {
            return ProofSettings.DEFAULT_SETTINGS.settingsToString().getBytes();
         }
      });

      dialog = new JDialog(parent, "Report an Error to KeY Developers",
            Dialog.ModalityType.DOCUMENT_MODAL);
      dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
      dialog.setBounds(parent.getBounds());

      JPanel right = new JPanel();
      right.setLayout(new BoxLayout(right, BoxLayout.Y_AXIS));
      for (SendFeedbackItem i : checkBoxes) {
         right.add(i.checkBox);
      }

      final JTextArea bugDescription = new JTextArea(20, 50);
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
               for (SendFeedbackItem item : checkBoxes) {
                  item.addZipEntry(stream);
               }
               stream.putNextEntry(new ZipEntry("bugDescription.txt"));
               stream.write(bugDescription.getText().getBytes());
               stream.closeEntry();
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
   }

   SendFeedbackAction(final Window parent, final Throwable exception) {
      this(parent);

      final JCheckBox sendErrorMessageCheckBox = new JCheckBox(
            "Send Error Message", true);
      SendFeedbackItem errorMessageFeedbackitem = new SendFeedbackItem(
            "errorMessage.txt", sendErrorMessageCheckBox) {
         @Override
         byte[] computeData() {
            return exception.getMessage().getBytes();
         }
      };

      final JCheckBox sendStackTraceCheckBox = new JCheckBox("Send Stacktrace",
            true);
      SendFeedbackItem stackTraceFeedbackItem = new SendFeedbackItem(
            "stacktrace.txt", sendStackTraceCheckBox) {
         @Override
         byte[] computeData() {
            return serializeStackTrace(exception).getBytes();
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
      dialog.pack();
      EditSourceFileAction.centerDialogRelativeToMainWindow(dialog);
      dialog.setVisible(true);
   }
}
