package de.uka.ilkd.key.gui;

import java.awt.Container;
import java.awt.Dialog;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedOutputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.util.LinkedList;
import java.util.List;
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

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ExceptionTools;
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

   // TODO provide a recipient e-mail address for developer feedback
   static final String FEEDBACK_RECIPIENT = null;

   // dialog that opens in case user wished to send feedback
   private final JDialog dialog;

   private static abstract class SendFeedbackItem {
      final JCheckBox checkBox;

      SendFeedbackItem(JCheckBox checkBox) {
         this.checkBox = checkBox;
      }

      /*
       * Override this in case "enabled" state of corresponding checkbox changes
       * dynamically.
       */
      boolean isEnabled() {
         return checkBox.isEnabled();
      }

      /*
       * Used when showing feedback dialog to disable checkboxes whose
       * corresponding metadata is not retrievable (e.g. no proof loaded).
       */
      void refreshEnabledProperty() {
         checkBox.setEnabled(isEnabled());
      }

      abstract void appendDataToZipOutputStream(ZipOutputStream stream)
            throws IOException;
   }

   private static abstract class SendFeedbackFileItem extends SendFeedbackItem {
      final String fileName;

      SendFeedbackFileItem(String fileName, JCheckBox checkBox) {
         super(checkBox);
         this.fileName = fileName;
      }

      abstract byte[] retrieveFileData() throws Exception;

      @Override
      void appendDataToZipOutputStream(ZipOutputStream stream)
            throws IOException {
         byte[] data;
         String zipEntryFileName = fileName;
         try {
            data = retrieveFileData();
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

   // checkboxes specifing which data will be contained in feedback
   private LinkedList<SendFeedbackItem> checkBoxes = new LinkedList<>();

   public SendFeedbackAction(final Window parent) {
      super("Send Feedback");

      checkBoxes.add(new SendFeedbackFileItem("lastLoadedProblem.key",
            new JCheckBox("Send Last Loaded Problem", true)) {
         @Override
         byte[] retrieveFileData() throws IOException {
            File mostRecentFile = new File(MainWindow.getInstance()
                  .getRecentFiles().getMostRecent().getAbsolutePath());
            return Files.readAllBytes(mostRecentFile.toPath());
         }

         @Override
         boolean isEnabled() {
            try {
               String file = MainWindow.getInstance().getRecentFiles()
                     .getMostRecent().getAbsolutePath();
               if (file == null || file.length() == 0) {
                  return false;
               }
               return true;
            }
            catch (Exception e) {
               return false;
            }
         }
      });

      checkBoxes.add(new SendFeedbackFileItem("keyVersion.txt", new JCheckBox(
            "Send KeY Version", true)) {
         @Override
         byte[] retrieveFileData() {
            return KeYConstants.VERSION.getBytes();
         }
      });

      checkBoxes.add(new SendFeedbackFileItem("systemProperties.txt",
            new JCheckBox("Send System Properties", true)) {
         @Override
         byte[] retrieveFileData() {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            System.getProperties().list(pw);
            String propsAsString = sw.getBuffer().toString();
            pw.close();
            return propsAsString.getBytes();
         }
      });

      checkBoxes.add(new SendFeedbackFileItem("openGoal.txt", new JCheckBox(
            "Send Open Goal", true)) {
         @Override
         byte[] retrieveFileData() {
            KeYMediator mediator = MainWindow.getInstance().getMediator();
            Goal goal = mediator.getSelectedGoal();
            return goal.toString().getBytes();
         }

         @Override
         boolean isEnabled() {
            try {
               MainWindow.getInstance().getMediator().getSelectedGoal();
               return true;
            }
            catch (Exception e) {
               return false;
            }
         }
      });

      checkBoxes.add(new SendFeedbackFileItem("openProof.proof", new JCheckBox(
            "Send Open Proof", true)) {
         @Override
         byte[] retrieveFileData() throws IOException {
            KeYMediator mediator = MainWindow.getInstance().getMediator();
            Proof proof = mediator.getSelectedProof();
            OutputStreamProofSaver saver = new OutputStreamProofSaver(proof);
            ByteArrayOutputStream stream = new ByteArrayOutputStream();
            saver.save(stream);
            return stream.toByteArray();
         }

         @Override
         boolean isEnabled() {
            try {
               Proof proof = MainWindow.getInstance().getMediator()
                     .getSelectedProof();
               return proof == null ? false : true;
            }
            catch (Exception e) {
               return false;
            }
         }
      });

      checkBoxes.add(new SendFeedbackFileItem("keySettings.txt", new JCheckBox(
            "Send KeY Settings", true)) {
         @Override
         byte[] retrieveFileData() {
            return ProofSettings.DEFAULT_SETTINGS.settingsToString().getBytes();
         }
      });

      checkBoxes.add(new SendFeedbackItem(new JCheckBox("Send Java Source",
            true)) {
         @Override
         boolean isEnabled() {
            try {
               File javaSourceLocation = MainWindow.getInstance().getMediator()
                     .getSelectedProof().getJavaSourceLocation();
               return javaSourceLocation == null ? false : true;
            }
            catch (Exception e) {
               return false;
            }
         }

         private void getJavaFilesRecursively(File directory, List<File> list) {
            for (File f : directory.listFiles()) {
               if (f.isDirectory()) {
                  getJavaFilesRecursively(f, list);
               }
               else if (f.getName().endsWith(".java")) {
                  list.add(f);
               }
            }
         }

         @Override
         void appendDataToZipOutputStream(ZipOutputStream stream)
               throws IOException {
            File javaSourceLocation = MainWindow.getInstance().getMediator()
                  .getSelectedProof().getJavaSourceLocation();
            List<File> javaFiles = new LinkedList<>();
            getJavaFilesRecursively(javaSourceLocation, javaFiles);
            for (File f : javaFiles) {
               stream.putNextEntry(new ZipEntry("javaSource/"
                     + javaSourceLocation.toURI().relativize(f.toURI())));
               stream.write(Files.readAllBytes(f.toPath()));
               stream.closeEntry();
            }
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
                              + FEEDBACK_RECIPIENT, "Send Bug Report",
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
                  if (item.checkBox.isSelected() && item.checkBox.isEnabled()) {
                     item.appendDataToZipOutputStream(stream);
                  }
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

      Location location = ExceptionTools.getLocation(exception);
      if (location != null) {
         final String sourceFileName = location.getFilename();
         if (sourceFileName != null) {
            checkBoxes.addFirst(new SendFeedbackFileItem(
                  "exceptionSourceFile.txt", new JCheckBox(
                        "Send Exception Source File", true)) {
               @Override
               byte[] retrieveFileData() throws IOException {
                  return Files.readAllBytes(new File(sourceFileName).toPath());
               }
            });
         }
      }

      final JCheckBox sendErrorMessageCheckBox = new JCheckBox(
            "Send Error Message", true);
      SendFeedbackFileItem errorMessageFeedbackitem = new SendFeedbackFileItem(
            "errorMessage.txt", sendErrorMessageCheckBox) {
         @Override
         byte[] retrieveFileData() {
            return exception.getMessage().getBytes();
         }
      };

      final JCheckBox sendStackTraceCheckBox = new JCheckBox("Send Stacktrace",
            true);
      SendFeedbackFileItem stackTraceFeedbackItem = new SendFeedbackFileItem(
            "stacktrace.txt", sendStackTraceCheckBox) {
         @Override
         byte[] retrieveFileData() {
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
      for (SendFeedbackItem i : checkBoxes) {
         i.refreshEnabledProperty();
      }
      dialog.pack();
      EditSourceFileAction.centerDialogRelativeToMainWindow(dialog);
      dialog.setVisible(true);
   }
}
