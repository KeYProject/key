package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYDesktop;
import de.uka.ilkd.key.gui.actions.EditSourceFileAction;
import de.uka.ilkd.key.gui.actions.SendFeedbackAction;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.sourceview.JavaDocument;
import de.uka.ilkd.key.gui.sourceview.TextLineNumber;
import de.uka.ilkd.key.gui.utilities.SquigglyUnderlinePainter;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExceptionTools;
import de.uka.ilkd.key.util.parsing.LocatableException;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.IOUtil;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.border.EmptyBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.SimpleAttributeSet;
import java.awt.*;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.event.KeyEvent;
import java.io.*;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Paths;
import java.util.List;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * A dialog for showing (possibly multiple) issues with a preview window. It can either display
 * multiple non-critical warnings, or a single critical exception.
 * <p>
 * This dialog has support to:
 * <ul>
 *     <li>hide listed warnings for the current session</li>
 *     <li>show the issue in a little preview window (with syntax highlighting)</li>
 *     <li>if an URL is in the description, it is possible to open this web page</li>
 *     <li>if a file name is associated with the warning, the user can open its editor</li>
 *     <li>if the message contains a stacktrace, it is optionally displayed</li>
 * </ul>
 *
 * @implNote The given PositionedStrings are assumed to have <b>1-based line and column numbers</b>,
 *           since this conforms to 1) the line numbers shown in the dialog and 2) the
 *           usual representation in text editors.
 *
 * @author Alexander Weigl
 * @author Wolfram Pfeifer: adaptations for also showing exceptions, making it the single dialog for
 *                          all parser error messages in KeY
 * @version 1 (6/8/21)
 * @version 2 (10/20/21)
 */
public final class IssueDialog extends JDialog {
    private static final Pattern HTTP_REGEX = Pattern.compile("https?://[^\\s]+");
    private static final Set<PositionedString> ignoredWarnings = new HashSet<>();

    private Throwable throwable;
    private final List<PositionedIssueString> warnings;
    private final Map<String, String> fileContentsCache = new HashMap<>();

    private final JTextField fTextField = new JTextField();
    private final JTextField lTextField = new JTextField();
    private final JTextField cTextField = new JTextField();
    private final JTextPane txtSource = new JTextPane();
    private final JTextArea txtStacktrace = new JTextArea();

    private final JList<PositionedIssueString> listWarnings;
    private final JButton btnFurtherInformation = new JButton("Further Information", IconFactory.help(16));
    private final JButton btnOpenFile = new JButton("Edit File", IconFactory.editFile(16));
    private final JCheckBox chkIgnoreWarnings = new JCheckBox("Ignore these warnings for the current session");
    private final JCheckBox chkDetails = new JCheckBox("Show Details");
    private final JSplitPane splitCenter = new JSplitPane(JSplitPane.VERTICAL_SPLIT, true) ;
    private final JSplitPane splitBottom = new JSplitPane(JSplitPane.VERTICAL_SPLIT, true);
    private final JPanel stacktracePanel = new JPanel(new BorderLayout());

    /** flag to switch between dialog for warnings and critical issues where parsing is aborted.
     * In the latter case only a single exception is show, which can also not be ignored */
    private final boolean critical;

    /** Reacts to selection events to the "Show details" checkbox (fold/unfold stacktrace). */
    private final transient ItemListener detailsBoxListener = e -> {
        int width = getWidth();
        int height = getHeight();
        if (e.getStateChange() == ItemEvent.SELECTED) {

            // the stacktrace gets a maximum height of 300px
            int stPrefHeight = Math.min(stacktracePanel.getPreferredSize().height, 300);
            setSize(new Dimension(width, height + stPrefHeight));
            int centerHeight = splitCenter.getHeight();
            // recalculate the sizes, in particular of the top component of splitBottom
            validate();
            // ensure that the top components look the same as before
            splitBottom.setDividerLocation(centerHeight + 1);
            splitBottom.setResizeWeight(0.66);
        } else {
            // ensure that the stacktrace stays minimized when resizing the dialog manually
            splitBottom.setDividerLocation(1.0);
            splitBottom.setResizeWeight(1.0);
            if (stacktracePanel.isShowing()) {
                // fold the stacktrace, but keep the rest of the dialog as is
                int stHeight = stacktracePanel.getHeight();
                setSize(new Dimension(width, height - stHeight));
            }
        }
        //repaint();        // not sure but this is probably not needed...
    };

    @Nullable
    private String urlFurtherInformation;

    private IssueDialog(Window owner, String title, Set<PositionedIssueString> issues,
                        boolean critical) {
        this(owner, title, issues, critical, null);
    }

    private IssueDialog(Window owner, String title, Set<PositionedIssueString> warnings,
                        boolean critical, Throwable throwable) {
        super(owner, title, ModalityType.APPLICATION_MODAL);

        this.throwable = throwable;
        this.critical = critical;

        setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        this.warnings = new ArrayList<>(warnings);
        this.warnings.sort(Comparator.comparing(o -> o.fileName));

        setLayout(new BorderLayout());

        // set descriptive text in top label
        final String head;
        if (critical) {
            head = "The following exception occurred:";
        } else {
            head = String.format(
                "The following non-fatal problems occurred when translating your %s specifications:",
                SLEnvInput.getLanguage());
        }
        JLabel label = new JLabel(head);
        label.setBorder(BorderFactory.createEmptyBorder(5, 5, 2, 5));
        add(label, BorderLayout.NORTH);

        Font font = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
        if (font == null) {
            // make sure a monospaced font is used
            font = new Font(Font.MONOSPACED, Font.PLAIN, 12);
        }

        // label
        //     scrWarnings
        //       listWarnings
        //   ----splitCenter
        //     sourcePanel
        //       locPanel: fTextField lTextField cTextField
        //       scrPreview: nowrap: txtSource
        //       pSouth
        //         chkIgnoreWarnings
        //         pButtons: btnOK btnFurtherInformation btnOpenFile chkDetails
        // ----splitBottom
        //   stacktracePanel
        //     stTextArea

        listWarnings = new JList<>(this.warnings.toArray(new PositionedIssueString[0]));

        JScrollPane scrWarnings = createWarningsPane(font);
        splitCenter.setTopComponent(scrWarnings);

        JPanel sourcePanel = createSourcePanel(font);
        splitCenter.setBottomComponent(sourcePanel);
        splitCenter.setDividerLocation(-1);
        splitCenter.setResizeWeight(0.5);
        splitCenter.setBorder(BorderFactory.createEmptyBorder(1, 1, 1, 1));

        splitBottom.setTopComponent(splitCenter);
        configureStacktracePanel(font);
        splitBottom.setBottomComponent(stacktracePanel);
        splitBottom.setBorder(BorderFactory.createEmptyBorder(1, 1, 1, 1));
        add(splitBottom, BorderLayout.CENTER);

        // minimizing the stacktrace unchecks the details checkbox
        splitBottom.addPropertyChangeListener(JSplitPane.DIVIDER_LOCATION_PROPERTY,
            e -> {
                // temporarily remove item listener to prevent infinite loop
                chkDetails.removeItemListener(detailsBoxListener);
                int newLoc = (int) e.getNewValue();
                chkDetails.setSelected(newLoc < splitBottom.getMaximumDividerLocation());
                chkDetails.addItemListener(detailsBoxListener);
            }
        );

        // ensures that the buttons fit into a single row
        setMinimumSize(new Dimension(630, 300));

        splitBottom.setDividerLocation(1.0);
        splitBottom.setResizeWeight(1.0);
        stacktracePanel.setMinimumSize(new Dimension(0, 0));

        // show the dialog with a size of 900*800 or smaller
        Dimension pref = getPreferredSize();
        Dimension minPref = new Dimension(Math.min(pref.width, 900), Math.min(pref.height, 800));
        setPreferredSize(minPref);

        pack();
        pack();
        chkDetails.setSelected(false);
        setLocationRelativeTo(owner);
    }

    // creates stacktrace area, but do not show
    private void configureStacktracePanel(Font font) {
        txtStacktrace.setFont(font);
        txtStacktrace.setEditable(false);
        txtStacktrace.setTabSize(4);
        txtStacktrace.setLineWrap(false);

        stacktracePanel.setBorder(BorderFactory.createTitledBorder("Stack Trace"));
        JScrollPane scrStacktrace = new JScrollPane(txtStacktrace);
        stacktracePanel.add(scrStacktrace);
    }

    private JScrollPane createWarningsPane(Font font) {
        // trigger updates of preview and stacktrace
        listWarnings.addListSelectionListener(e -> updatePreview(listWarnings.getSelectedValue()));
        listWarnings.addListSelectionListener(e -> updateStackTrace(listWarnings.getSelectedValue()));
        // enable/disable "further information", "open file", and "show details"
        listWarnings.addListSelectionListener(
            e -> updateFurtherInformation(listWarnings.getSelectedValue().text));
        listWarnings.addListSelectionListener(e ->
            btnOpenFile.setEnabled(listWarnings.getSelectedValue().hasFilename()));
        listWarnings.addListSelectionListener(e -> {
            if (listWarnings.getSelectedValue().additionalInfo.isEmpty()) {
                chkDetails.setSelected(false);
                chkDetails.setEnabled(false);
                /* disable the bottom split and hide the divider (we can not use setEnabled(false)
                 * on the splitpane because this has side effects on some children!) */
                splitBottom.setDividerSize(0);
                stacktracePanel.setVisible(false);
            } else {
                // enable the bottom split and show the divider
                splitBottom.setDividerSize(splitCenter.getDividerSize());
                stacktracePanel.setVisible(true);
                chkDetails.setEnabled(true);
            }
            repaint();
        });
        listWarnings.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        listWarnings.setCellRenderer(new PositionedStringRenderer());
        listWarnings.setSelectedIndex(0);

        JScrollPane scrWarnings;
        if (warnings.size() == 1) {
            JTextArea issueTextArea = new JTextArea();
            issueTextArea.setEditable(false);
            issueTextArea.setTabSize(4);
            issueTextArea.setLineWrap(false);
            issueTextArea.setFont(font);
            PositionedString value = this.warnings.get(0);
            issueTextArea.setText(value.text);
            scrWarnings = new JScrollPane(issueTextArea);
            // ensure that the start of the error message is visible
            issueTextArea.setCaretPosition(0);
        } else {
            scrWarnings = new JScrollPane(listWarnings);
        }
        return scrWarnings;
    }

    private JPanel createSourcePanel(Font font) {
        txtSource.setEditable(false);
        txtSource.setFont(font);

        // workaround to disable automatic line wrapping and enable horizontal scrollbar instead
        JPanel nowrap = new JPanel(new BorderLayout());
        nowrap.add(txtSource);
        JScrollPane scrPreview = new JScrollPane();
        scrPreview.setViewportView(nowrap);
        scrPreview.getVerticalScrollBar().setUnitIncrement(30);
        scrPreview.getHorizontalScrollBar().setUnitIncrement(30);

        TextLineNumber lineNumbers = new TextLineNumber(txtSource, 2);
        scrPreview.setRowHeaderView(lineNumbers);

        final JButton btnOK = new JButton("OK");
        btnOK.addActionListener(e -> accept());
        Dimension buttonDim = new Dimension(100, 27);
        btnOK.setPreferredSize(buttonDim);
        btnOK.setMinimumSize(buttonDim);
        btnOK.setMaximumSize(new Dimension(Integer.MAX_VALUE, 27));

        final JButton btnSendFeedback = new JButton(new SendFeedbackAction(this, throwable));
        Dimension feedbackBtnDim = new Dimension(130, buttonDim.height);
        btnSendFeedback.setMinimumSize(feedbackBtnDim);
        btnSendFeedback.setPreferredSize(feedbackBtnDim);

        Box pSouth = new Box(BoxLayout.Y_AXIS);
        JPanel pButtons = new JPanel(new FlowLayout(FlowLayout.CENTER));
        pButtons.add(btnOK);
        pButtons.add(btnFurtherInformation);
        pButtons.add(btnOpenFile);
        pButtons.add(btnSendFeedback);
        pButtons.add(chkDetails);

        chkDetails.addItemListener(detailsBoxListener);

        btnFurtherInformation.addActionListener(e -> {
            if (urlFurtherInformation != null && !urlFurtherInformation.isEmpty()) {
                try {
                    Objects.requireNonNull(Desktop.getDesktop())
                        .browse(URI.create(urlFurtherInformation));
                } catch (IOException ex) {
                    JOptionPane.showMessageDialog(IssueDialog.this, ex.getMessage());
                }
            }
        });

        EditSourceFileAction action = new EditSourceFileAction(this, throwable);
        btnOpenFile.addActionListener(action);

        /*
        btnOpenFile.addActionListener(e -> {
            final PositionedString selectedValue = listWarnings.getSelectedValue();
            if (selectedValue.hasFilename()) {
                try {
                    Objects.requireNonNull(Desktop.getDesktop())
                        .open(new File(selectedValue.fileName));
                } catch (IOException ex) {
                    JOptionPane.showMessageDialog(IssueDialog.this, ex.getMessage());
                }
            }
        });
         */

        btnOK.registerKeyboardAction(
            event -> {
                if (event.getActionCommand().equals("ESC")) {
                    btnOK.doClick();
                }
            },
            "ESC",
            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
            JComponent.WHEN_IN_FOCUSED_WINDOW);

        // by default, do not ignore any warnings
        chkIgnoreWarnings.setSelected(false);
        if (!critical) {
            pSouth.add(chkIgnoreWarnings);
        }
        pSouth.add(pButtons);
        getRootPane().setDefaultButton(btnOK);

        JPanel sourcePanel = new JPanel(new BorderLayout());
        JPanel locPanel = new JPanel();

        fTextField.setEditable(false);
        lTextField.setEditable(false);
        cTextField.setEditable(false);
        locPanel.add(fTextField);
        locPanel.add(lTextField);
        locPanel.add(cTextField);

        sourcePanel.add(locPanel, BorderLayout.NORTH);
        sourcePanel.add(scrPreview);
        sourcePanel.add(pSouth, BorderLayout.SOUTH);
        return sourcePanel;
    }

    public static void showExceptionDialog(Window parent, Throwable exception) {
        Set<PositionedIssueString> msg = Collections.singleton(extractMessage(exception));
        IssueDialog dlg = new IssueDialog(parent, "Parser Error", msg, true, exception);
        dlg.setVisible(true);
        dlg.dispose();
    }

    public static void showWarningsIfNecessary(MainWindow mainWindow, ImmutableSet<PositionedString> warnings) {
        Set<PositionedString> warn = warnings.toSet();
        warn.removeAll(ignoredWarnings);
        // do not show warnings dialog if all warnings are ignored
        if (!warn.isEmpty()) {
            // ensure that each warning has at least an empty additionalInfo
            Set<PositionedIssueString> issues = warnings.stream()
                .map(o -> o instanceof PositionedIssueString ? (PositionedIssueString)o
                    : new PositionedIssueString(o, ""))
                .collect(Collectors.toSet());

            IssueDialog dialog = new IssueDialog(mainWindow,
                SLEnvInput.getLanguage() + " warning(s)", issues, false);
            dialog.setVisible(true);
            dialog.dispose();
        }
    }

    private static PositionedIssueString extractMessage(Throwable exception) {
        try (StringWriter sw = new StringWriter()) {
            PrintWriter pw = new PrintWriter(sw);
            Location location = ExceptionTools.getLocation(exception);
            exception.printStackTrace(pw);
            String message = exception.getMessage();
            String info = sw.toString();
            String filename = "";
            Position pos = Position.UNDEFINED;
            if (Location.isValidLocation(location)) {
                 filename = new File(location.getFileURL().toURI()).toString();
                 pos = new Position(location.getLine(), location.getColumn());
            }
            return new PositionedIssueString(message, filename, pos, info);
        } catch (URISyntaxException | IOException e) {
            // We must not suppress the dialog here -> catch and print only to debug stream
            Debug.out("Creating a Location failed for " + exception, e);
        }
        return new PositionedIssueString("Constructing the error message failed!");
    }

    private void accept() {
        if (!critical && chkIgnoreWarnings.isSelected()) {
            ignoredWarnings.addAll(warnings);
        }
        setVisible(false);
    }

    /**
     * Small data class that in addition to the information already contained by PositionedString
     * (text, filename, position) contains a String for additional information which can be used
     * to store a stacktrace if present.
     */
    private static class PositionedIssueString extends PositionedString {

        /** contains additional information, e.g., a stacktrace */
        private final @Nonnull String additionalInfo;

        public PositionedIssueString(@Nonnull String text, @Nullable String fileName,
                                     @Nullable Position pos, @Nonnull String additionalInfo) {
            super(text, fileName, pos);
            this.additionalInfo = additionalInfo;
        }

        public PositionedIssueString(@Nonnull String text) {
            this(text, null, null, "");
        }

        public PositionedIssueString(@Nonnull PositionedString o, @Nonnull String additionalInfo) {
            this(o.text, o.fileName, o.pos, additionalInfo);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) {
                return true;
            }
            if (o == null || getClass() != o.getClass()) {
                return false;
            }
            if (!super.equals(o)) {
                return false;
            }
            PositionedIssueString that = (PositionedIssueString) o;
            return additionalInfo.equals(that.additionalInfo);
        }

        @Override
        public int hashCode() {
            return Objects.hash(super.hashCode(), additionalInfo);
        }
    }

    private void updatePreview(PositionedIssueString issue) {
        // update text fields with position information
        if (!issue.fileName.isEmpty()) {
            fTextField.setText("File: " + issue.fileName);
        } else {
            fTextField.setText("");
        }
        cTextField.setText("Column: " + issue.pos.getColumn());
        lTextField.setText("Line: " + issue.pos.getLine());

        btnOpenFile.setEnabled(issue.pos != Position.UNDEFINED);

        try {
            String source = fileContentsCache.computeIfAbsent(issue.fileName, fn -> {
                try (InputStream stream = IOUtil.openStream(issue.fileName)) {
                    return IOUtil.readFrom(stream);
                } catch (IOException e) {
                    Debug.out("Unknown IOException!", e);
                    return "[SOURCE COULD NOT BE LOADED]\n" + e.getMessage();
                }
            });

            if (isJava(issue.fileName)) {
                showJavaSourceCode(source);
            } else {
                txtSource.setText(source);
            }
            DefaultHighlighter dh = new DefaultHighlighter();
            txtSource.setHighlighter(dh);
            addHighlights(dh, issue.fileName);

            // ensure that the currently selected problem is shown in view
            int offset = getOffsetFromLineColumn(source, issue.pos);
            txtSource.setCaretPosition(offset);
        } catch (Exception e) {
            e.printStackTrace();
        }
        validate();
    }

    private void updateStackTrace(PositionedIssueString issue) {
        txtStacktrace.setText(issue.additionalInfo);
    }

    private void showJavaSourceCode(String source) {
        try {
            JavaDocument doc = new JavaDocument();
            txtSource.setDocument(doc);
            doc.insertString(0, source, new SimpleAttributeSet());
        } catch (BadLocationException e) {
            throw new RuntimeException(e);
        }
    }

    private void addHighlights(DefaultHighlighter dh, String fileName) {
        warnings.stream()
                .filter(ps -> fileName.equals(ps.fileName))
                .forEach(ps -> addHighlights(dh, ps));
    }

    private void addHighlights(DefaultHighlighter dh, PositionedString ps) {
        String source = txtSource.getText();
        int offset = getOffsetFromLineColumn(source, ps.pos);
        int end = offset;
        while (end < source.length() && !Character.isWhitespace(source.charAt(end))) {
            end++;
        }
        try {
            if (critical) {
                dh.addHighlight(offset, end,
                    new SquigglyUnderlinePainter(Color.RED, 2, 1f));
            } else {
                dh.addHighlight(offset, end,
                    new SquigglyUnderlinePainter(Color.ORANGE, 2, 1f));
            }
        } catch (BadLocationException ignore) {
            // ignore
        }
    }


    private void updateFurtherInformation(String text) {
        Matcher m = HTTP_REGEX.matcher(text);
        if (m.find()) {
            this.urlFurtherInformation = m.group();
            btnFurtherInformation.setEnabled(true);
        } else {
            btnFurtherInformation.setEnabled(false);
        }
    }

    private boolean isJava(String fileName) {
        return fileName.endsWith(".java");
    }

    // as far as I can tell, this method treats lines and columns as zero-based
    public static int getOffsetFromLineColumn(String source, Position pos) {
        // Position has 1-based line and column, we need them 0-based
        return getOffsetFromLineColumn(source, pos.getLine() - 1, pos.getColumn() - 1);
    }

    private static int getOffsetFromLineColumn(String source, int line, int column) {
        if (line < 0) throw new IllegalArgumentException();
        if (column < 0) throw new IllegalArgumentException();

        int pos = 0;
        char[] c = source.toCharArray();
        for (; pos < c.length && line > 0; ++pos) {
            if (c[pos] == '\n') {
                --line;
            }
        }
        if (line == 0) return pos + column;

        throw new ArrayIndexOutOfBoundsException("Given position is out of bounds.");
    }


    private static class PositionedStringRenderer implements ListCellRenderer<PositionedString> {
        private final JTextArea area = new JTextArea(5, 69);
        private final JPanel panel = new JPanel();

        PositionedStringRenderer() {
            area.setLineWrap(true);
            area.setWrapStyleWord(true);
            BoxLayout layout = new BoxLayout(panel, BoxLayout.Y_AXIS);
            panel.setLayout(layout);
            panel.add(area);
        }


        @Override
        public Component getListCellRendererComponent(JList<? extends PositionedString> list, PositionedString value,
                                                      int index, boolean isSelected, boolean cellHasFocus) {
            area.setText(value.text);
            area.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
            if (isSelected) {
                area.setBackground(list.getSelectionBackground());
                area.setForeground(list.getSelectionForeground());
            } else {
                area.setBackground(list.getBackground());
                area.setForeground(list.getForeground());
            }

            area.setEnabled(list.isEnabled());
            area.setFont(list.getFont());

            Border border = null;
            if (cellHasFocus) {
                if (isSelected) {
                    border = UIManager.getBorder("List.focusSelectedCellHighlightBorder");
                }
                if (border == null) {
                    border = UIManager.getBorder("List.focusCellHighlightBorder");
                }
            } else {
                border = new EmptyBorder(1, 1, 1, 1);
            }
            panel.setBorder(border);

            return panel;
        }
    }

    //Debugging
    public static void main(String[] args) {
        PositionedIssueString a = new PositionedIssueString("Multiline text\nTest\n",
                    "/home/wolfram/Desktop/key/key/key.ui/src/main/java/de/uka/ilkd/key/gui/TaskTree.java",
                    new Position(20, 25), "");
        PositionedIssueString b = new PositionedIssueString("Multiline text\nTest\n More information: https://google.de",
                    "/home/wolfram/Desktop/key/key/key.ui/src/main/java/de/uka/ilkd/key/gui/SearchBar.java",
                    new Position(35, 10), "");
        PositionedIssueString c = new PositionedIssueString("Blubb",
                    "/home/wolfram/Desktop/key/key/key.ui/src/main/java/de/uka/ilkd/key/gui/SearchBar.java",
                    new Position(36, 1), "");

        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        warnings = warnings.add(a);
        warnings = warnings.add(b);
        warnings = warnings.add(c);
        Exception npe = new NullPointerException("Fake Null Pointer exception");
        try {
            Location loc = new Location(Paths.get("/home/wolfram/Desktop/key/key/key.ui/src/main/java/de/uka/ilkd/key/gui/SearchBar.java").toUri().toURL(), 35, 10);
            Exception e = new LocatableException("Fake locatable Exception", npe, loc);
            PositionedIssueString pis = extractMessage(e);
            warnings = warnings.add(extractMessage(e));
            IssueDialog.showWarningsIfNecessary(null, warnings);
            //IssueDialog.showExceptionDialog(null, e);
        } catch (MalformedURLException e) {
            e.printStackTrace();
        }
    }
}
