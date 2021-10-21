package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.*;
import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Timer;
import java.util.TimerTask;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.JTextComponent;
import javax.swing.text.SimpleAttributeSet;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.sourceview.JavaDocument;
import de.uka.ilkd.key.gui.sourceview.TextLineNumber;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.ExceptionTools;
import org.key_project.util.java.IOUtil;

/**
 * Used by {@link ExceptionDialog} to open the source file containing an error
 * for editing.
 *
 * @author Kai Wallisch
 */
@Deprecated
public class EditSourceFileAction extends AbstractAction {
    private static final long serialVersionUID = -2540941448174197032L;

    /** tooltip of save buttons and textarea if the file is not writeable
     * (e.g. inside a zip archive) */
    private static final String READONLY_TOOLTIP = "The resource is readonly, " +
            "probably the URL points into a zip/jar archive!";

    /** The parent window. */
    private final Window parent;
    /** The exception. */
    private final Throwable exception;

    /**
     * Instantiates a new edits the source file action.
     *
     * @param parent the parent
     * @param exception the exception
     */
    public EditSourceFileAction(final Window parent, final Throwable exception) {
        super("Edit Source File");
        this.parent = parent;
        this.exception = exception;
    }

    /**
     * Moves the caret in a {@link JTextArea} to the specified position. Assumes
     * the first position in the textarea is in line 1 column 1.
     */
    private static void textAreaGoto(JTextComponent textArea, int line, int col) {
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

    private static JTextPane createTextArea(final Location location,
                                            final int columnNumber) throws IOException {

        // final JTextArea textArea = new JTextArea(30, columnNumber) {
        final JTextPane textPane = new JTextPane() {
            private static final long serialVersionUID = 1L;

            @Override
            public void addNotify() {
                super.addNotify();
                requestFocus();
                textAreaGoto(this, location.getLine(), location.getColumn());
            }
        };
        // read the content via URLs openStream() method
        String source = IOUtil.readFrom(location.getFileURL().openStream());

        if (location.getFileURL().toString().endsWith(".java")) {
            JavaDocument doc = new JavaDocument();
            try {
                doc.insertString(0, source, new SimpleAttributeSet());
            } catch (BadLocationException e) {
                e.printStackTrace();
            }
            textPane.setDocument(doc);

            // when no key is pressed for 0.8 seconds, update (redo) the syntax highlighting
            textPane.addKeyListener(new KeyAdapter() {
                Timer timer = new Timer();

                @Override
                public void keyPressed(KeyEvent e) {
                    restartTimer();
                }

                @Override
                public void keyReleased(KeyEvent e) {
                    restartTimer();
                }

                @Override
                public void keyTyped(KeyEvent e) {
                    //restartTimer();
                }

                private void restartTimer() {
                    timer.cancel();
                    timer = new Timer();
                    final TimerTask task = new TimerTask() {
                        @Override
                        public void run() {
                            int pos = textPane.getCaretPosition();
                            String content = textPane.getText();
                            try {
                                // creating a completely new document seems to be more than
                                // necessary, but works well enough for the moment
                                JavaDocument newDoc = new JavaDocument();
                                newDoc.insertString(0, content, new SimpleAttributeSet());
                                textPane.setDocument(newDoc);
                                textPane.setCaretPosition(pos);
                            } catch (BadLocationException ex) {
                                ex.printStackTrace();
                            }
                            textPane.repaint();
                        }
                    };
                    timer.schedule(task, 800);
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

        /*
        textArea.setText(source);
        textArea.setFont(ExceptionDialog.MESSAGE_FONT);
        textArea.setLineWrap(false);
        textArea.setBorder(new TitledBorder(location.getFileURL().toString()));
        return textArea;
         */
    }


    private static File tryGetFile(URL sourceURL) {
        File sourceFile = null;
        if (sourceURL != null && sourceURL.getProtocol().equals("file")) {
            try {
                sourceFile = Paths.get(sourceURL.toURI()).toFile();
            } catch (URISyntaxException e) {
                // TODO: error reporting
                e.printStackTrace();
            }
        }
        return sourceFile;
    }

    private JPanel createButtonPanel(final URL sourceURL,
                                     //final JTextArea textArea,
                                     final JTextPane textPane,
                                     final JDialog dialog) {
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout());
        JButton saveButton = new JButton("Save");
        JButton reloadButton = new JButton("Save, Close and Reload");
        JButton cancelButton = new JButton("Cancel");
        ActionListener closeAction = new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent arg0) {
                dialog.dispose();
            }
        };
        cancelButton.addActionListener(closeAction);

        final File sourceFile = tryGetFile(sourceURL);
        if (sourceFile == null) {
            // make content read-only and show tooltips
            saveButton.setEnabled(false);
            reloadButton.setEnabled(false);
            textPane.setEditable(false);
            saveButton.setToolTipText(READONLY_TOOLTIP);
            reloadButton.setToolTipText(READONLY_TOOLTIP);
            textPane.setToolTipText(READONLY_TOOLTIP);
        } else {
            ActionListener saveAction = new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent arg0) {
                    try {
                        Files.write(sourceFile.toPath(), textPane.getText().getBytes());
                    } catch (IOException ioe) {
                        String message = "Cannot write to file:\n" + ioe.getMessage();
                        JOptionPane.showMessageDialog(parent, message);
                    }
                }
            };
            ActionListener reloadAction = new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent arg0) {
                    parent.setVisible(false);
                    MainWindow.getInstance().loadProblem(sourceFile);
                }
            };
            saveButton.addActionListener(saveAction);
            reloadButton.addActionListener(saveAction);
            reloadButton.addActionListener(closeAction);
            reloadButton.addActionListener(reloadAction);
        }

        buttonPanel.add(saveButton);
        buttonPanel.add(cancelButton);
        buttonPanel.add(reloadButton);
        return buttonPanel;
    }

    @Override
    public void actionPerformed(ActionEvent arg0) {
        try {
            final Location location = ExceptionTools.getLocation(exception);
            if (!Location.isValidLocation(location)) {
                throw new IOException("Cannot recover file location from exception.");
            }

            // indicate edit/readonly in dialog title
            String prefix;
            if (tryGetFile(location.getFileURL()) != null) {
                prefix = "Edit ";
            } else {
                prefix = "[Readonly] ";
            }
            final JDialog dialog = new JDialog(parent, prefix + location.getFileURL(),
                    Dialog.ModalityType.DOCUMENT_MODAL);
            dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);

            final int columnNumber = 75;

            final JScrollPane parserMessageScrollPane =
                    createParserMessageScrollPane(exception, columnNumber);

            //final JTextArea textArea = createTextArea(location, columnNumber);
            final JTextPane txtSource = createTextArea(location, columnNumber);

            // workaround to disable automatic line wrapping and enable horizontal scrollbar instead
            JPanel nowrap = new JPanel(new BorderLayout());
            nowrap.add(txtSource);
            JScrollPane scrSource = new JScrollPane();
            scrSource.setViewportView(nowrap);
            scrSource.getVerticalScrollBar().setUnitIncrement(30);
            scrSource.getHorizontalScrollBar().setUnitIncrement(30);
            scrSource.setBorder(new TitledBorder(location.getFileURL().toString()));

            TextLineNumber lineNumbers = new TextLineNumber(txtSource, 2);
            scrSource.setRowHeaderView(lineNumbers);
            //JScrollPane textAreaScrollPane = new JScrollPane(textArea);

            scrSource.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
            scrSource
                .setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

            JPanel buttonPanel = createButtonPanel(location.getFileURL(), txtSource, dialog);

            Container container = dialog.getContentPane();
            //container.setLayout(new BoxLayout(container, BoxLayout.Y_AXIS));
            JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
            splitPane.setTopComponent(parserMessageScrollPane);
            splitPane.setBottomComponent(scrSource);
            container.add(splitPane, BorderLayout.CENTER);
            container.add(buttonPanel, BorderLayout.SOUTH);

            dialog.pack();
            centerDialogRelativeToMainWindow(dialog);
            dialog.setVisible(true);
        } catch (IOException ioe) {
            String message = "Cannot open file:\n" + ioe.getMessage();
            JOptionPane.showMessageDialog(parent, message);
        }
    }

    /**
     * Center dialog relative to main window.
     *
     * @param dialog the dialog
     */
    static void centerDialogRelativeToMainWindow(final JDialog dialog) {
        dialog.setLocationRelativeTo(MainWindow.getInstance());
//      Rectangle bounds = dialog.getBounds();
//      Rectangle mainWindowBounds = MainWindow.getInstance().getBounds();
//      int x = Math.max(0, mainWindowBounds.x
//            + (mainWindowBounds.width - bounds.width) / 2);
//      int y = Math.max(0, mainWindowBounds.y
//            + (mainWindowBounds.height - bounds.height) / 2);
//      dialog.setBounds(x, y, bounds.width, bounds.height);
    }
}
