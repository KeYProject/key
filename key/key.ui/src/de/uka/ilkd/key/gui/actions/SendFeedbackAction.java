package de.uka.ilkd.key.gui.actions;

import java.awt.Container;
import java.awt.Desktop;
import java.awt.Dialog;
import java.awt.FlowLayout;
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
import java.net.URI;
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
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
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
@SuppressWarnings("serial")
public class SendFeedbackAction extends AbstractAction {

    /*
     * This is the email address to which feedback will be sent.
     */
    private static final String FEEDBACK_RECIPIENT = "feedback@key-project.org";

    private static String serializeStackTrace(Throwable t) {
        StringWriter sw = new StringWriter();
        t.printStackTrace(new PrintWriter(sw));
        return sw.toString();
    }

    private static abstract class SendFeedbackItem implements ActionListener {

        final String displayName;
        private boolean selected = true;

        SendFeedbackItem(String displayName) {
            this.displayName = displayName;
        }

        /*
         * Override this in case "enabled" changes.
         */
        boolean isEnabled() {
            return true;
        }

        boolean isSelected() {
            return selected;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            selected = ((JCheckBox)e.getSource()).isSelected();
        }

        abstract void appendDataToZipOutputStream(ZipOutputStream stream)
                throws IOException;

    }

    private static abstract class SendFeedbackFileItem extends SendFeedbackItem {
        final String fileName;

        SendFeedbackFileItem(String displayName, String fileName) {
            super(displayName);
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

    private static class LastLoadedProblemItem extends SendFeedbackFileItem {

        LastLoadedProblemItem() {
            super("Send Last Loaded Problem", "lastLoadedProblem.key");
        }

        @Override
        byte[] retrieveFileData() throws Exception {
            File mostRecentFile = new File(MainWindow.getInstance()
                    .getRecentFiles().getMostRecent().getAbsolutePath());
            return Files.readAllBytes(mostRecentFile.toPath());
        }

        @Override
        boolean isEnabled() {
            try {
                String file = MainWindow.getInstance().
                        getRecentFiles().getMostRecent().getAbsolutePath();
                if (file == null || file.length() == 0) {
                    return false;
                }
                return true;
            }
            catch (Exception e) {
                return false;
            }
        }

    }

    private static class VersionItem extends SendFeedbackFileItem {
        VersionItem() {
            super("Send KeY Version", "keyVersion.txt");
        }

        @Override
        byte[] retrieveFileData() {
            return KeYConstants.VERSION.getBytes();
        }
    }

    private static class SystemPropertiesItem extends SendFeedbackFileItem {
        SystemPropertiesItem() {
            super("Send System Properties", "systemProperties.txt");
        }

        @Override
        byte[] retrieveFileData() {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            System.getProperties().list(pw);
            String propsAsString = sw.getBuffer().toString();
            pw.close();
            return propsAsString.getBytes();
        }
    }

    private class OpenGoalItem extends SendFeedbackFileItem {
        OpenGoalItem() {
            super("Send Open Goal", "openGoal.txt");
        }

        @Override
        byte[] retrieveFileData() {
            KeYMediator mediator = MainWindow.getInstance().getMediator();
            Goal goal = mediator.getSelectedGoal();
            return goal.toString().getBytes();
        }

        @Override
        boolean isEnabled() {
            try {
                Goal g = MainWindow.getInstance().getMediator().getSelectedGoal();
                return g != null;
            } catch (Exception e) {
                return false;
            }
        }
    }

    private class OpenProofItem extends SendFeedbackFileItem {
        OpenProofItem() {
            super("Send Open Proof", "openProof.proof");
        }

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
            } catch (Exception e) {
                return false;
            }
        }
    }

    private static class SettingsItem extends SendFeedbackFileItem {
        SettingsItem() {
            super("Send KeY Settings", "keySettings.txt");
        }

        @Override
        byte[] retrieveFileData() {
            return ProofSettings.DEFAULT_SETTINGS.settingsToString().getBytes();
        }
    }

    private class StacktraceItem extends SendFeedbackFileItem {
        StacktraceItem() {
            super("Send Stacktrace", "stacktrace.txt");
        }

        @Override
        boolean isEnabled() {
            return throwable != null;
        }

        @Override
        byte[] retrieveFileData() {
           return serializeStackTrace(throwable).getBytes();
        }
    }

    private class FaultyFileItem extends SendFeedbackFileItem {
        FaultyFileItem() {
            super("Send File Exception points to", "exceptionSourceFile.txt");
        }

        @Override
        boolean isEnabled() {
            if(throwable != null) {
                Location location = ExceptionTools.getLocation(throwable);
                return location != null && location.getFilename() != null;
            }
            return false;
        }

        @Override
        byte[] retrieveFileData() throws IOException {
            Location location = ExceptionTools.getLocation(throwable);
            String sourceFileName = location.getFilename();
            return Files.readAllBytes(new File(sourceFileName).toPath());
        }
    }


    private static class JavaSourceItem extends SendFeedbackItem {
        public JavaSourceItem() {
            super("Send Java Source");
        }
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
    }

    private class SendAction implements ActionListener {
        private static final String MAIL_BODY =
                "Please attach the file %s with the chosen metadata to this mail and send it.%%0a%%0a" +
                "Thanks for your feedack, %%0athe KeY team";

        JDialog dialog;
        JTextArea message;

        public SendAction(JDialog dialog, JTextArea bugDescription) {
            this.dialog = dialog;
            this.message = bugDescription;
        }

        @Override
        public void actionPerformed(ActionEvent arg0) {

            try {
                File reportFile = File.createTempFile("key-bugreport", ".zip");

                int confirmed = JOptionPane.showConfirmDialog(
                        parent,
                        "A zip archive containing the selected data will be created.\n"
                                + "A new e-mail client window will open.\n"
                                + "Please attach the file " + reportFile +
                                " to the mail and send it.", "Send Bug Report",
                                JOptionPane.OK_CANCEL_OPTION);

                if (confirmed == JOptionPane.OK_OPTION) {
                    saveMetaDataToFile(reportFile, message.getText());
                    if (Desktop.isDesktopSupported()) {
                        Desktop desktop = Desktop.getDesktop();
                        URI uriMailTo = new URI("mailto:" + FEEDBACK_RECIPIENT + "?" +
                                "subject=KeY%20feedback&body=" +
                                String.format(MAIL_BODY, reportFile).replace(" ", "%20"));
                        desktop.mail(uriMailTo);
                    } else {
                        JOptionPane.showMessageDialog(parent,
                                "A mail window cannot be automatically opened on your system.\n"+
                                "Please send the file " + reportFile + " to address " +
                                FEEDBACK_RECIPIENT);
                    }
                }
            } catch (Exception e) {
                ExceptionDialog.showDialog(parent, e);
            }

            dialog.dispose();
        }
    }

    private void saveMetaDataToFile(File zipFile, String message) throws IOException {

        ZipOutputStream stream = null;
        try {
            stream = new ZipOutputStream(new BufferedOutputStream(
                    new FileOutputStream(zipFile)));
            for (SendFeedbackItem item : items) {
                if (item.isSelected() && item.isEnabled()) {
                    item.appendDataToZipOutputStream(stream);
                }
            }
            stream.putNextEntry(new ZipEntry("bugDescription.txt"));
            stream.write(message.getBytes());
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

    private final SendFeedbackItem items[] = {
            new StacktraceItem(),
            new FaultyFileItem(),
            new LastLoadedProblemItem(),
            new VersionItem(),
            new SystemPropertiesItem(),
            new OpenGoalItem(),
            new OpenProofItem(),
            new SettingsItem(),
            new JavaSourceItem()
    };

    private final Throwable throwable;
    private final Window parent;

    public SendFeedbackAction(final Window parent) {
        this(parent, null);
    }

    public SendFeedbackAction(final Window parent, final Throwable exception) {
        this.parent = parent;
        putValue(NAME, "Send feedback");
        this.throwable = exception;
    }

    private JDialog makeDialog() {

        final JDialog dialog = new JDialog(parent, "Report an Error to KeY Developers",
                Dialog.ModalityType.DOCUMENT_MODAL);
        dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);

        JPanel right = new JPanel();
        right.setLayout(new BoxLayout(right, BoxLayout.Y_AXIS));
        for (SendFeedbackItem item : items) {
            JCheckBox box = new JCheckBox(item.displayName);
            if(item.isEnabled()) {
                box.setSelected(item.isSelected());
                box.addActionListener(item);
            } else {
                box.setSelected(false);
                box.setEnabled(false);
            }
            right.add(box);
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
        buttonPanel.setLayout(new FlowLayout());

        JButton sendFeedbackReportButton = new JButton("Send Feedback");
        sendFeedbackReportButton.addActionListener(new SendAction(dialog, bugDescription));

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

        return dialog;
    }

    @Override
    public void actionPerformed(ActionEvent event) {
        JDialog dialog = makeDialog();
        dialog.setLocationRelativeTo(parent);
        dialog.setVisible(true);
    }
}
