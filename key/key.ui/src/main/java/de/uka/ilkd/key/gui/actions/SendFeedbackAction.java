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
import java.net.MalformedURLException;
import java.net.URI;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.util.LinkedList;
import java.util.List;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.filechooser.FileFilter;

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
import org.key_project.util.java.IOUtil;

/**
 * {@link AbstractAction} used by {@link ExceptionDialog} in KeY report error
 * button was pressed.
 *
 * @author Kai Wallisch
 *
 */
public class SendFeedbackAction extends AbstractAction {

    private static final long serialVersionUID = 8146108238901822515L;

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
            super("Send last loaded problem", "lastLoadedProblem.key");
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
            super("Send KeY version", "keyVersion.txt");
        }

        @Override
        byte[] retrieveFileData() {
            return KeYConstants.VERSION.getBytes();
        }
    }

    private static class SystemPropertiesItem extends SendFeedbackFileItem {
        SystemPropertiesItem() {
            super("Send system properties", "systemProperties.txt");
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
            super("Send open proof goal", "openGoal.txt");
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
            super("Send open proof", "openProof.proof");
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
            super("Send KeY settings", "keySettings.txt");
        }

        @Override
        byte[] retrieveFileData() {
            return ProofSettings.DEFAULT_SETTINGS.settingsToString().getBytes();
        }
    }

    private class StacktraceItem extends SendFeedbackFileItem {
        StacktraceItem() {
            super("Send stacktrace", "stacktrace.txt");
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
            super("Send file referenced by exception", "exceptionSourceFile.txt");
        }

        @Override
        boolean isEnabled() {
            if(throwable != null) {
                Location location = null;
                try {
                    location = ExceptionTools.getLocation(throwable);
                } catch (MalformedURLException e) {
                    // no valid location could be extracted
                    e.printStackTrace();
                    return false;
                }
                return Location.isValidLocation(location);
            }
            return false;
        }

        @Override
        byte[] retrieveFileData() throws IOException {
            Location location = ExceptionTools.getLocation(throwable);
            /* Certainly there are more efficient methods than reading to string with IOUtil
             * (using default charset) and then writing back to byte[] (using default charset
             * again). However, this way it is a very concise and easy to read. */
            String source = IOUtil.readFrom(location.getFileURL());
            return source.getBytes(Charset.defaultCharset());
        }
    }


    private static class JavaSourceItem extends SendFeedbackItem {
        public JavaSourceItem() {
            super("Send Java source");
        }

        @Override
        boolean isEnabled() {
            try {
                Proof proof = MainWindow.getInstance().getMediator()
                        .getSelectedProof();
                File javaSourceLocation = OutputStreamProofSaver.getJavaSourceLocation(proof);
                return javaSourceLocation == null ? false : true;
            } catch (Exception e) {
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
           Proof proof = MainWindow.getInstance().getMediator()
                         .getSelectedProof();
           File javaSourceLocation = OutputStreamProofSaver.getJavaSourceLocation(proof);
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
        private final JDialog dialog;
        private final JTextArea message;

        public SendAction(JDialog dialog, JTextArea bugDescription) {
            this.dialog = dialog;
            this.message = bugDescription;
        }

        @Override
        public void actionPerformed(ActionEvent arg0) {

            try {
                int confirmed = JOptionPane.showConfirmDialog(
                        parent,
                        "A zip archive containing the selected data will be created.\n"
                                + "To report a problem, send it in an e-mail to the KeY developers\n"
                                + "at " + FEEDBACK_RECIPIENT + ".", "Send Bug Report",
                        JOptionPane.OK_CANCEL_OPTION);

                if(confirmed != JOptionPane.OK_OPTION) {
                    return;
                }

                JFileChooser jfc = new JFileChooser();
                jfc.addChoosableFileFilter(new FileFilter() {
                    @Override
                    public boolean accept(File f) {
                        return f.getName().toLowerCase().endsWith(".zip");
                    }

                    @Override
                    public String getDescription() {
                        return "ZIP archives";
                    }
                });

                int answer = jfc.showSaveDialog(parent);
                if (answer == JFileChooser.APPROVE_OPTION) {
                    saveMetaDataToFile(jfc.getSelectedFile(), message.getText());
                    JOptionPane.showMessageDialog(parent,
                            String.format("Your message has been saved to the file %s.",
                                    jfc.getSelectedFile()));
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

        final JDialog dialog = new JDialog(parent, "Report an error to KeY developers",
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
