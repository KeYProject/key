/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Optional;
import java.util.Timer;
import java.util.TimerTask;
import javax.annotation.Nullable;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.JTextComponent;
import javax.swing.text.SimpleAttributeSet;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.sourceview.JavaDocument;
import de.uka.ilkd.key.gui.sourceview.TextLineNumber;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.ExceptionTools;

import org.key_project.util.java.IOUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Used by {@link de.uka.ilkd.key.gui.IssueDialog} to open the source file containing an error for
 * editing. In particular, the cursor is moved directly to the location of the issue. For Java
 * files, also syntax highlighting is supported (refreshes when nothing has been typed for some
 * milliseconds in the editor).
 *
 * @author Kai Wallisch
 * @author Wolfram Pfeifer: syntax highlighting
 */
public class EditSourceFileAction extends KeyAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(EditSourceFileAction.class);
    /**
     * tooltip of save buttons and textarea if the file is not writeable (e.g. inside a zip archive)
     */
    private static final String READONLY_TOOLTIP =
        "The resource is readonly, " + "probably the URL points into a zip/jar archive!";

    /**
     * The interval in milliseconds for refreshing the syntax highlighting of the shown file: If
     * after a change in the text field no other char is pressed for this period, the document is
     * completely re-highlighted. If desired, this could be set much lower (also seems to work with
     * ~50).
     */
    private static final int SYNTAX_HIGHLIGHTING_REFRESH_INTERVAL = 800;

    /**
     * The parent window.
     */
    private final Window parent;
    /**
     * The exception.
     */
    private final Throwable exception;

    /**
     * Instantiates a new edits the source file action.
     *
     * @param parent the parent
     * @param exception the exception
     */
    public EditSourceFileAction(final Window parent, final Throwable exception) {
        setName("Edit File");
        setIcon(IconFactory.editFile(16));
        this.parent = parent;
        this.exception = exception;
        setEnabled(exception != null);
    }

    /**
     * Moves the caret in a {@link JTextArea} to the specified position. Assumes the first position
     * in the textarea is in line 1 column 1.
     */
    private static void textAreaGoto(JTextComponent textArea, Position position) {
        int line = position.line();
        int col = position.column();
        String text = textArea.getText();
        int i = 0;
        while (i < text.length() && line > 1) {
            if (text.charAt(i) == '\n') {
                line--;
            }
            i++;
        }
        i += col - 1;
        if (i > textArea.getDocument().getLength()) {
            i = textArea.getDocument().getLength();
        }
        textArea.setCaretPosition(i);
    }

    private static JScrollPane createParserMessageScrollPane(final Throwable exception,
            final int columnNumber) {
        JTextArea parserMessage = new JTextArea();
        String message = exception.getMessage();
        message = message == null ? "" : message;
        parserMessage.setText(message);
        parserMessage.setEditable(false);
        parserMessage.setColumns(columnNumber);
        // approximate # rows
        parserMessage.setRows(message.length() / (columnNumber - 10));
        parserMessage.setLineWrap(true);
        parserMessage.setWrapStyleWord(true);
        parserMessage.setBorder(new TitledBorder("Parser Message"));
        JScrollPane parserMessageScrollPane = new JScrollPane(parserMessage);
        parserMessageScrollPane
                .setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
        parserMessageScrollPane
                .setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        return parserMessageScrollPane;
    }

    private JTextPane createSrcTextPane(final Location location) throws IOException {
        final JTextPane textPane = new JTextPane() {
            @Override
            public void addNotify() {
                super.addNotify();
                requestFocus();
                textAreaGoto(this, location.getPosition());
            }
        };
        Optional<URI> file = location.getFileURI();
        String source = IOUtil.readFrom(file.orElse(null)).orElse("");
        // workaround for #1641: replace all carriage returns, since JavaDocument can currently
        // not handle them
        source = source.replace("\r", "");

        if (file.isPresent() && file.get().toString().endsWith(".java")) {
            JavaDocument doc = new JavaDocument();
            try {
                doc.insertString(0, source, new SimpleAttributeSet());
            } catch (BadLocationException e) {
                LOGGER.warn("Failed insert string", e);
            }
            textPane.setDocument(doc);

            // when no char is inserted for the specified interval, refresh the syntax highlighting
            // note: When other keys are pressed or held down (e.g. arrow keys) nothing is done.
            textPane.addKeyListener(new KeyAdapter() {
                private Timer timer = new Timer();

                @Override
                public void keyTyped(KeyEvent e) {
                    restartTimer();
                }

                private void restartTimer() {
                    timer.cancel();
                    timer = new Timer();
                    final TimerTask task = new TimerTask() {
                        @Override
                        public void run() {
                            // synchronized to avoid inserting chars during document updating
                            synchronized (textPane) {
                                int pos = textPane.getCaretPosition();
                                int start = textPane.getSelectionStart();
                                int end = textPane.getSelectionEnd();
                                String content = textPane.getText();
                                try {
                                    // creating a completely new document seems to be more than
                                    // necessary, but works well enough for the moment
                                    JavaDocument newDoc = new JavaDocument();
                                    newDoc.insertString(0, content, new SimpleAttributeSet());
                                    textPane.setDocument(newDoc);
                                    textPane.setCaretPosition(pos);
                                    textPane.setSelectionStart(start);
                                    textPane.setSelectionEnd(end);
                                } catch (BadLocationException ex) {
                                    LOGGER.warn("Failed update document", ex);
                                }
                                textPane.repaint();
                            }
                        }
                    };
                    timer.schedule(task, SYNTAX_HIGHLIGHTING_REFRESH_INTERVAL);
                }
            });
        } else {
            textPane.setText(source);
        }

        Font font = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
        if (font == null) {
            // make sure a monospaced font is used
            font = new Font(Font.MONOSPACED, Font.PLAIN, 12);
        }
        textPane.setFont(font);
        return textPane;
    }

    private static @Nullable File tryGetFile(@Nullable URI sourceURL) {
        File sourceFile = null;
        if (sourceURL != null && sourceURL.getScheme().equals("file")) {
            sourceFile = Paths.get(sourceURL).toFile();
        }
        return sourceFile;
    }

    private JPanel createButtonPanel(final URI sourceURI, final JTextPane textPane,
            final JDialog dialog) {
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout());
        JButton saveButton = new JButton("Save");
        JButton reloadButton = new JButton("Save, Close and Reload");
        JButton cancelButton = new JButton("Cancel");
        ActionListener closeAction = event -> dialog.dispose();
        cancelButton.addActionListener(closeAction);

        final File sourceFile = tryGetFile(sourceURI);
        if (sourceFile == null) {
            // make content read-only and show tooltips
            saveButton.setEnabled(false);
            reloadButton.setEnabled(false);
            textPane.setEditable(false);
            saveButton.setToolTipText(READONLY_TOOLTIP);
            reloadButton.setToolTipText(READONLY_TOOLTIP);
            textPane.setToolTipText(READONLY_TOOLTIP);
        } else {
            ActionListener saveAction = event -> {
                try {
                    // workaround for #1641: replace "\n" with system dependent line separators when
                    // saving
                    String text = textPane.getText().replace("\n", System.lineSeparator());
                    Files.write(sourceFile.toPath(), text.getBytes(StandardCharsets.UTF_8));
                } catch (IOException ioe) {
                    String message = "Cannot write to file:\n" + ioe.getMessage();
                    JOptionPane.showMessageDialog(parent, message);
                }
            };
            ActionListener reloadAction = event -> {
                parent.setVisible(false);
                MainWindow.getInstance().loadProblem(sourceFile);
            };
            saveButton.addActionListener(saveAction);
            reloadButton.addActionListener(event -> {
                saveAction.actionPerformed(event);
                closeAction.actionPerformed(event);
                reloadAction.actionPerformed(event);
            });
        }

        buttonPanel.add(saveButton);
        buttonPanel.add(cancelButton);
        buttonPanel.add(reloadButton);
        return buttonPanel;
    }

    @Override
    public void actionPerformed(ActionEvent arg0) {
        if (exception == null) {
            JOptionPane.showMessageDialog(
                SwingUtilities.windowForComponent((Component) arg0.getSource()),
                "The given exception does not carry any positional information.",
                "Position not available", JOptionPane.ERROR_MESSAGE);
            return;
        }

        try {
            final Location location = ExceptionTools.getLocation(exception)
                    .filter(l -> l.getFileURI().isPresent())
                    .orElseThrow(
                        () -> new IOException("Cannot recover file location from exception."));
            final URI uri = location.getFileURI().orElseThrow();

            // indicate edit/readonly in dialog title
            String prefix;
            if (tryGetFile(uri) != null) {
                prefix = "Edit ";
            } else {
                prefix = "[Readonly] ";
            }
            final JDialog dialog = new JDialog(parent, prefix + uri,
                Dialog.ModalityType.DOCUMENT_MODAL);
            dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);

            final int columnNumber = 75;

            final JScrollPane parserMessageScrollPane =
                createParserMessageScrollPane(exception, columnNumber);

            final JTextPane txtSource = createSrcTextPane(location);

            // workaround to disable automatic line wrapping and enable horizontal scrollbar instead
            JPanel nowrap = new JPanel(new BorderLayout());
            nowrap.add(txtSource);
            JScrollPane sourceScrollPane = new JScrollPane();
            sourceScrollPane.setViewportView(nowrap);
            sourceScrollPane.getVerticalScrollBar().setUnitIncrement(30);
            sourceScrollPane.getHorizontalScrollBar().setUnitIncrement(30);
            sourceScrollPane.setBorder(new TitledBorder(uri.toString()));

            TextLineNumber lineNumbers = new TextLineNumber(txtSource, 2);
            sourceScrollPane.setRowHeaderView(lineNumbers);

            sourceScrollPane
                    .setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
            sourceScrollPane.setHorizontalScrollBarPolicy(
                ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

            JPanel buttonPanel = createButtonPanel(uri, txtSource, dialog);

            Container container = dialog.getContentPane();
            JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
            splitPane.setTopComponent(parserMessageScrollPane);
            splitPane.setBottomComponent(sourceScrollPane);
            container.add(splitPane, BorderLayout.CENTER);
            container.add(buttonPanel, BorderLayout.SOUTH);

            dialog.pack();
            int screenWidth = Toolkit.getDefaultToolkit().getScreenSize().width - 25;
            int screenHeight = Toolkit.getDefaultToolkit().getScreenSize().height - 25;
            int width = Math.min(dialog.getWidth(), screenWidth);
            int height = Math.min(dialog.getHeight(), screenHeight);
            dialog.setSize(width, height);

            dialog.setLocationRelativeTo(parent);
            dialog.setVisible(true);
        } catch (IOException ioe) {
            String message = "Cannot open file:\n" + ioe.getMessage();
            JOptionPane.showMessageDialog(parent, message);
        }
    }
}
