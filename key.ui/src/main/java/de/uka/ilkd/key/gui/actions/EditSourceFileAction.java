/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Optional;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.JTextComponent;
import javax.swing.text.SimpleAttributeSet;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.sourceview.JavaJMLEditorLexer;
import de.uka.ilkd.key.gui.sourceview.KeYEditorLexer;
import de.uka.ilkd.key.gui.sourceview.SourceHighlightDocument;
import de.uka.ilkd.key.gui.sourceview.TextLineNumber;
import de.uka.ilkd.key.gui.utilities.CurrentLineHighlighter;
import de.uka.ilkd.key.util.ExceptionTools;

import org.key_project.util.java.IOUtil;
import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;

import org.jspecify.annotations.Nullable;
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
     * The exception (when constructed from one); {@code null} when an explicit location was given.
     */
    private final Throwable exception;
    /** explicit location to open at; overrides the one derived from {@link #exception} */
    private final Location overrideLocation;
    /** message to show next to the source when {@link #overrideLocation} is used */
    private final String overrideMessage;

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
        this.overrideLocation = null;
        this.overrideMessage = null;
        setEnabled(exception != null);
    }

    /**
     * Opens the editor directly at the given location. Used to jump to a <em>specific</em> issue
     * when several are reported, so the editor opens at the selected issue rather than the first.
     *
     * @param parent the parent window
     * @param location the location to open and place the caret at
     * @param message the message to show next to the source
     */
    public EditSourceFileAction(final Window parent, final Location location,
            final String message) {
        setName("Edit File");
        setIcon(IconFactory.editFile(16));
        this.parent = parent;
        this.exception = null;
        this.overrideLocation = location;
        this.overrideMessage = message == null ? "" : message;
        setEnabled(location != null && location.getFileUri() != null
                && !location.getPosition().isNegative());
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

    private static JScrollPane createParserMessageScrollPane(final String message,
            final int columnNumber) {
        JTextArea parserMessage = new JTextArea();
        String msg = message == null ? "" : message;
        parserMessage.setText(msg);
        parserMessage.setEditable(false);
        parserMessage.setColumns(columnNumber);
        // approximate # rows
        parserMessage.setRows(Math.max(1, msg.length() / (columnNumber - 10)));
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
        textPane.setHighlighter(new CurrentLineHighlighter(textPane.getHighlighter()));
        Optional<URI> fileOpt = location.getFileURI();
        if (fileOpt.isEmpty()) {
            JTextPane jTextPane = new JTextPane();
            jTextPane.setText("No file location available");
            return jTextPane;
        }

        URI file = fileOpt.get();
        String source = IOUtil.readFrom(file);
        // workaround for #1641: replace all carriage returns, since JavaDocument can currently
        // not handle them
        source = source != null ? source.replace("\r", "") : "";

        SourceHighlightDocument.EditorLexer lexer;
        if (file.toString().endsWith(".java")) {
            lexer = new JavaJMLEditorLexer();
        } else if (file.toString().endsWith(".key") || file.toString().endsWith(".proof")) {
            lexer = new KeYEditorLexer();
        } else {
            lexer = SourceHighlightDocument.TRIVIAL_LEXER;
        }

        SourceHighlightDocument doc = new SourceHighlightDocument(lexer);
        try {
            doc.insertString(0, source, new SimpleAttributeSet());
        } catch (BadLocationException e) {
            LOGGER.warn("Failed insert string", e);
        }
        textPane.setDocument(doc);

        Font font = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
        if (font == null) {
            // make sure a monospaced font is used
            font = new Font(Font.MONOSPACED, Font.PLAIN, 12);
        }
        textPane.setFont(font);
        return textPane;
    }

    private static Path tryGetFile(@Nullable URI sourceURL) {
        Path sourceFile = null;
        if (sourceURL != null && sourceURL.getScheme().equals("file")) {
            sourceFile = Paths.get(sourceURL);
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

        final Path sourceFile = tryGetFile(sourceURI);
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
                    Files.writeString(sourceFile, text);
                } catch (IOException ioe) {
                    String message = "Cannot write to file:\n" + ioe.getMessage();
                    JOptionPane.showMessageDialog(parent, message);
                }
            };
            ActionListener reloadAction = event -> {
                parent.setVisible(false);
                // Reload the original problem (e.g. the .key file together with its \includes),
                // NOT the edited source file itself. sourceFile is the file the error pointed at
                // (often a .java source); loading that bare file would drop the problem's includes
                // and user-defined symbols, so a spec that is actually fine then fails with a
                // misleading "Unknown escaped symbol ..." Reload the most-recently-opened problem
                // instead - it is recorded at load start, so it is still available even though the
                // current load failed - and fall back to the source file only if none is known.
                var recentFiles = MainWindow.getInstance().getRecentFiles();
                String mostRecent = recentFiles != null ? recentFiles.getMostRecent() : null;
                Path problemFile = mostRecent != null ? Paths.get(mostRecent) : sourceFile;
                MainWindow.getInstance().loadProblem(problemFile);
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
        try {
            final Location location;
            final String message;
            if (overrideLocation != null) {
                location = overrideLocation;
                message = overrideMessage;
            } else if (exception != null) {
                location = ExceptionTools.getLocation(exception);
                message = exception.getMessage() == null ? "" : exception.getMessage();
            } else {
                location = null;
                message = "";
            }
            if (location == null || location.getFileUri() == null) {
                JOptionPane.showMessageDialog(
                    SwingUtilities.windowForComponent((Component) arg0.getSource()),
                    "The given problem does not carry any positional information.",
                    "Position not available", JOptionPane.ERROR_MESSAGE);
                return;
            }
            final URI uri = location.getFileUri();

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
                createParserMessageScrollPane(message, columnNumber);

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
