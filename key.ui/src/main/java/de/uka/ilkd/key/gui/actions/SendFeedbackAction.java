/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.*;
import java.net.HttpURLConnection;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLConnection;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.filechooser.FileFilter;
import javax.swing.text.html.HTMLEditorKit;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ExceptionTools;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;

import org.key_project.util.Streams;
import org.key_project.util.java.IOUtil;
import org.key_project.util.parsing.Location;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Action that executes if "Send Feedback..." was pressed. There are currently two locations: In
 * {@link IssueDialog} and in the main menu {@link MenuSendFeedackAction}.
 * <p>
 * For a documentation of the backend of the auto-send mechanism, refer to the file key-report.php
 * in the same directory as this file.
 *
 * @author Kai Wallisch, Mattias Ulbrich
 *
 */
@NullMarked
public class SendFeedbackAction extends AbstractAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(SendFeedbackAction.class);

    /*
     * This is the email address to which feedback will be sent.
     */
    private static final String FEEDBACK_RECIPIENT = "support@key-project.org";

    /**
     * This is the url to which the feedback will be sent.
     */
    private static final String REPORT_URL = "https://formal.kastel.kit.edu/key/key-report.php";

    private static String serializeStackTrace(Throwable t) {
        StringWriter sw = new StringWriter();
        t.printStackTrace(new PrintWriter(sw));
        return sw.toString();
    }

    /**
     * Extracts java source directory from {@link Proof#header()}, if it exists.
     *
     * @param proof the Proof
     * @return the location of the java source code or null if no such exists
     */
    public static @Nullable Path getJavaSourceLocation(Proof proof) {
        KeyAst.@Nullable Declarations header = proof.header();
        if (header == null)
            return null;
        return header.getJavaSourceLocation();
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
            selected = ((JCheckBox) e.getSource()).isSelected();
        }

        abstract void appendDataToZipOutputStream(ZipOutputStream stream) throws IOException;

    }

    private static abstract class SendFeedbackFileItem extends SendFeedbackItem {
        final String fileName;

        SendFeedbackFileItem(String displayName, String fileName) {
            super(displayName);
            this.fileName = fileName;
        }

        abstract byte[] retrieveFileData() throws Exception;

        @Override
        void appendDataToZipOutputStream(ZipOutputStream stream) throws IOException {
            byte[] data;
            String zipEntryFileName = fileName;
            try {
                data = retrieveFileData();
            } catch (Exception e) {
                zipEntryFileName += ".exception";
                data = (e.getClass().getSimpleName() + " occured while trying to read data.\n"
                    + e.getMessage() + "\n" + serializeStackTrace(e))
                        .getBytes(StandardCharsets.UTF_8);
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
            String mostRecent = MainWindow.getInstance().getRecentFiles().getMostRecent();
            if (mostRecent == null) {
                // Only enabled when a most-recent file exists; a {@code null} here is a
                // concurrent state change, crash-equivalent to the previous {@code null} into the
                // {@code File} constructor.
                throw new NullPointerException("No recently opened file to send.");
            }
            File mostRecentFile = new File(mostRecent);
            return Files.readAllBytes(mostRecentFile.toPath());
        }

        @Override
        boolean isEnabled() {
            try {
                String file =
                    MainWindow.getInstance().getRecentFiles().getMostRecent();
                return file != null && file.length() != 0;
            } catch (Exception e) {
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
            return KeYConstants.VERSION.getBytes(StandardCharsets.UTF_8);
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
            return propsAsString.getBytes(StandardCharsets.UTF_8);
        }
    }

    private static class OpenGoalItem extends SendFeedbackFileItem {
        OpenGoalItem() {
            super("Send open proof goal", "openGoal.txt");
        }

        @Override
        byte[] retrieveFileData() {
            KeYMediator mediator = MainWindow.getInstance().getMediator();
            Goal goal = mediator.getSelectedGoal();
            if (goal == null) {
                // Only enabled while a goal is selected (see {@link #isEnabled()}); a {@code null}
                // here is a concurrent state change, crash-equivalent to the previous NPE.
                throw new NullPointerException("No goal selected to send.");
            }
            return goal.toString().getBytes(StandardCharsets.UTF_8);
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

    private static class OpenProofItem extends SendFeedbackFileItem {
        OpenProofItem() {
            super("Send open proof", "openProof.proof");
        }

        @Override
        byte[] retrieveFileData() throws IOException {
            KeYMediator mediator = MainWindow.getInstance().getMediator();
            Proof proof = mediator.getSelectedProof();
            if (proof == null) {
                // Only enabled while a proof is loaded (see {@link #isEnabled()}); a {@code null}
                // here is a concurrent state change, crash-equivalent to the previous NPE in the
                // saver.
                throw new NullPointerException("No proof loaded to send.");
            }
            OutputStreamProofSaver saver = new OutputStreamProofSaver(proof);
            ByteArrayOutputStream stream = new ByteArrayOutputStream();
            saver.save(Paths.get(".").toAbsolutePath(), stream);
            return stream.toByteArray();
        }

        @Override
        boolean isEnabled() {
            try {
                Proof proof = MainWindow.getInstance().getMediator().getSelectedProof();
                return proof != null;
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
            return ProofSettings.DEFAULT_SETTINGS.settingsToString()
                    .getBytes(StandardCharsets.UTF_8);
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
            Throwable t = throwable;
            if (t == null) {
                // Only enabled when the exception is set (see {@link #isEnabled()}); a {@code
                // null} here is impossible, guarded for the checker.
                throw new NullPointerException("No stack trace to send.");
            }
            return serializeStackTrace(t).getBytes(StandardCharsets.UTF_8);
        }
    }

    private class FaultyFileItem extends SendFeedbackFileItem {
        FaultyFileItem() {
            super("Send file referenced by exception", "exceptionSourceFile.txt");
        }

        @Override
        boolean isEnabled() {
            if (throwable != null) {
                try {
                    var location = ExceptionTools.getLocation(throwable);
                    return location != null && location.getFileURI().isPresent();
                } catch (MalformedURLException e) {
                    // no valid location could be extracted
                    LOGGER.warn("Failed to extract location", e);
                    return false;
                }
            }
            return false;
        }

        @Override
        byte[] retrieveFileData() throws IOException {
            /*
             * Certainly there are more efficient methods than reading to string with IOUtil (using
             * default charset) and then writing back to byte[] (using default charset again).
             * However, this way it is a very concise and easy to read.
             */
            Throwable t = throwable;
            if (t == null) {
                // Only enabled when the exception is set (see {@link #isEnabled()}); a {@code
                // null} here is impossible, guarded for the checker.
                throw new NullPointerException("No exception source file to send.");
            }
            Location url = ExceptionTools.getLocation(t);
            if (url != null) {
                String content = IOUtil.readFrom(url.fileUri());
                if (content == null) {
                    // {@code readFrom} fails to read the resource; the previous code crashed in
                    // {@code getBytes} on such input, keep that behavior.
                    throw new IOException("Could not read the exception source file.");
                }
                return content.getBytes(Charset.defaultCharset());
            }
            return new byte[0];
        }
    }

    private static class JavaSourceItem extends SendFeedbackItem {
        public JavaSourceItem() {
            super("Send Java source");
        }

        @Override
        boolean isEnabled() {
            try {
                Proof proof = MainWindow.getInstance().getMediator().getSelectedProof();
                Path javaSourceLocation = proof != null ? getJavaSourceLocation(proof) : null;
                return javaSourceLocation != null;
            } catch (Exception e) {
                return false;
            }
        }

        private List<Path> getJavaFilesRecursively(Path directory) {
            try (var stream = Files.walk(directory)) {
                return stream
                        .filter(it -> it.toString().endsWith(".java")
                                || it.toString().endsWith(".jml"))
                        .toList();
            } catch (IOException e) {
                return List.of();
            }
        }

        @Override
        void appendDataToZipOutputStream(ZipOutputStream stream) throws IOException {
            Proof proof = MainWindow.getInstance().getMediator().getSelectedProof();
            if (proof == null) {
                // Only enabled while a proof is loaded (see {@link #isEnabled()}); a {@code null}
                // here is a concurrent state change, crash-equivalent to the previous NPE.
                throw new NullPointerException("No proof loaded to send its Java sources.");
            }
            Path javaSourceLocation = getJavaSourceLocation(proof);
            if (javaSourceLocation == null) {
                // No Java source location is attached to the proof (see {@link
                // #getJavaSourceLocation}); sending nothing mirrors the previous NPE-free
                // behavior of an empty source section.
                return;
            }
            List<Path> javaFiles = getJavaFilesRecursively(javaSourceLocation);
            for (Path f : javaFiles) {
                stream.putNextEntry(
                    new ZipEntry("javaSource/" + javaSourceLocation.relativize(f)));
                stream.write(Files.readAllBytes(f));
                stream.closeEntry();
            }
        }
    }

    private void saveZIP(String message) {
        try {
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
                File selectedFile = jfc.getSelectedFile();
                if (selectedFile == null) {
                    throw new NullPointerException("No file selected in the file chooser.");
                }
                saveMetaDataToFile(selectedFile, message);
                JOptionPane.showMessageDialog(parent,
                    String.format("Your message has been saved to the file %s.\n"
                        + "If you want to report a bug, you can enclose this file in an\n"
                        + "e-mail to " + FEEDBACK_RECIPIENT + ".", selectedFile));
            }
        } catch (Exception e) {
            LOGGER.error("", e);
            IssueDialog.showExceptionDialog(parent, e);
        }
    }

    private void sendReport(String message) {

        String[] msgs = {
            // tp.setEditable(false);
            // tp.setBackground(UIManager.getColor("label.background"));
            // tp.setEditorKit(new HTMLEditorKit());
            // tp.setText("<html>" +
            "The data you have collected and the description text will now be sent via",
            "https to the server formal.kastel.kit.edu, stored on the server and forwarded",
            "to the KeY mailing list.", "", "Click OK if you want to send the report now." };
        int answer = JOptionPane.showConfirmDialog(parent, msgs, "Ready to send?",
            JOptionPane.YES_NO_OPTION);
        if (answer != JOptionPane.YES_OPTION) {
            return;
        }

        try {
            ByteArrayOutputStream buffer = new ByteArrayOutputStream();
            saveMetaData(buffer, message);
            URLConnection connection = new URL(REPORT_URL).openConnection();
            connection.setDoOutput(true);
            connection.setRequestProperty("Content-Type", "application/zip");
            connection.setRequestProperty("KeY-Version",
                "KeY " + KeYResourceManager.getManager().getVersion());
            try (OutputStream os = connection.getOutputStream()) {
                os.write(buffer.toByteArray());
            }
            connection.connect();
            int responseCode = ((HttpURLConnection) connection).getResponseCode();

            if (responseCode == 200) {
                JOptionPane.showMessageDialog(parent, "Your report has been filed successfully.");
            } else {
                String msg = Streams.toString(((HttpURLConnection) connection).getErrorStream());
                throw new IOException(
                    "The server responded with an error message (" + responseCode + "): " + msg);
            }

        } catch (Exception e) {
            LOGGER.error("", e);
            IssueDialog.showExceptionDialog(parent, e);
        }
    }

    private void saveMetaDataToFile(File zipFile, String message) throws IOException {
        try (FileOutputStream fos = new FileOutputStream(zipFile)) {
            saveMetaData(fos, message);
        }
    }

    private void saveMetaData(OutputStream os, String message) throws IOException {
        try (ZipOutputStream stream = new ZipOutputStream(new BufferedOutputStream(os))) {
            for (SendFeedbackItem item : items) {
                if (item.isSelected() && item.isEnabled()) {
                    item.appendDataToZipOutputStream(stream);
                }
            }
            stream.putNextEntry(new ZipEntry("bugDescription.txt"));
            stream.write(message.getBytes(StandardCharsets.UTF_8));
            stream.closeEntry();
        } catch (FileNotFoundException e) {
            JOptionPane.showMessageDialog(parent, e.getMessage());
        }
    }

    private final SendFeedbackItem[] items = { new StacktraceItem(), new FaultyFileItem(),
        new LastLoadedProblemItem(), new VersionItem(), new SystemPropertiesItem(),
        new OpenGoalItem(), new OpenProofItem(), new SettingsItem(), new JavaSourceItem() };

    private final @Nullable Throwable throwable;
    private final Window parent;

    public SendFeedbackAction(final Window parent) {
        this(parent, null);
    }

    /**
     * The action-configuration setter is called on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public SendFeedbackAction(final Window parent, final @Nullable Throwable exception) {
        this.parent = parent;
        putValue(NAME, "Send feedback...");
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
            if (item.isEnabled()) {
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

        JButton saveFeedbackReportButton = new JButton("Save Feedback...");
        saveFeedbackReportButton.setToolTipText(
            "<html>Information about current proof state are saved to a file.<br>"
                + "This file can be also used when reporting a bug via e-mail.");
        saveFeedbackReportButton.addActionListener(e -> {
            saveZIP(bugDescription.getText());
            dialog.dispose();
        });

        JButton sendFeedbackReportButton = new JButton("Send Feedback...");
        sendFeedbackReportButton
                .setToolTipText("<html>Information about current proof state are sent via a "
                    + "secure https connection to the developers.<br>"
                    + "The receiving server is located at KIT (formal.kastel.kit.edu).");
        sendFeedbackReportButton.addActionListener(e -> {
            sendReport(bugDescription.getText());
            dialog.dispose();
        });

        JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(e -> dialog.dispose());

        buttonPanel.add(saveFeedbackReportButton);
        buttonPanel.add(sendFeedbackReportButton);
        buttonPanel.add(cancelButton);

        JTextPane labels = new JTextPane();
        labels.setEditorKit(new HTMLEditorKit());
        labels.setEditable(false);
        labels.setBackground(UIManager.getColor("Label.background"));
        labels.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
        labels.setText(
            "<html>The report feature can be used to send information about your current state of KeY to report a bug or to ask for advice from the KeY team.<br>"
                + "You can either store the information in a zip locally (and then e.g. send that via e-mail to "
                + FEEDBACK_RECIPIENT + ") or send directly to our server.<br>"
                + "Please select the information that you want to include from the list on the right.<br>"
                + "If you send the information directly, <b>please make sure to indicate your e-mail address</b> "
                + "in the message below such that the team can respond.");
        Container container = dialog.getContentPane();
        container.setLayout(new BorderLayout());
        container.add(labels, BorderLayout.NORTH);
        container.add(topPanel, BorderLayout.CENTER);
        container.add(buttonPanel, BorderLayout.SOUTH);

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
