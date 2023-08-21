/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.*;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.util.*;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import javax.swing.*;
import javax.swing.event.HyperlinkEvent;
import javax.swing.text.*;
import javax.swing.text.html.HTML;
import javax.swing.text.html.HTMLDocument;

import de.uka.ilkd.key.gui.actions.EditSourceFileAction;
import de.uka.ilkd.key.gui.actions.SendFeedbackAction;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.sourceview.JavaDocument;
import de.uka.ilkd.key.gui.sourceview.TextLineNumber;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.gui.utilities.SquigglyUnderlinePainter;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.ExceptionTools;

import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A dialog for showing (possibly multiple) issues with a preview window. It can either display
 * multiple non-critical warnings, or a single critical exception.
 * <p>
 * This dialog has support to:
 * <ul>
 * <li>hide listed warnings for the current session</li>
 * <li>show the issue in a little preview window (with syntax highlighting)</li>
 * <li>if an URL is in the description, it is possible to open this web page</li>
 * <li>if a file name is associated with the warning, the user can open its editor</li>
 * <li>if the message contains a stacktrace, it is optionally displayed</li>
 * </ul>
 *
 * @implNote The given PositionedStrings are assumed to have <b>1-based line and column numbers</b>,
 *           since this conforms to 1) the line numbers shown in the dialog and 2) the usual
 *           representation in text editors.
 *
 * @author Alexander Weigl
 * @author Wolfram Pfeifer: adaptations for also showing exceptions, making it the single dialog for
 *         all parser error messages in KeY
 * @version 1 (6/8/21)
 * @version 2 (11/15/21)
 */
public final class IssueDialog extends JDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(IssueDialog.class);

    /**
     * Default text for critical issues (runtime exceptions).
     */
    private static final String CRITICAL_ISSUE = "The following exception occurred:";
    /**
     * Default text for non-critical issues (JML specification warnings).
     */
    private static final String NON_CRITICAL_ISSUE = String.format(
        "The following non-fatal problems occurred when translating your %s specifications:",
        SLEnvInput.getLanguage());

    /** regex to find web urls in string messages */
    private static final Pattern HTTP_REGEX = Pattern.compile("https?://[^\\s]+");

    /** warnings which have been marked to be ignored by the user (in this KeY run) */
    private static final Set<PositionedString> ignoredWarnings = new HashSet<>();

    /** the single critical issue that is shown in this dialog */
    private final Throwable throwable;

    /** the warnings that are shown in this dialog */
    private final List<PositionedIssueString> warnings;

    private final Map<URI, String> fileContentsCache = new HashMap<>();

    private final JTextField fTextField = new JTextField();
    private final JTextField lTextField = new JTextField();
    private final JTextField cTextField = new JTextField();
    private final JTextPane txtSource = new JTextPane();
    private final JTextArea txtStacktrace = new JTextArea();

    private final JList<PositionedIssueString> listWarnings;

    private final JButton btnEditFile = new JButton();
    private final JCheckBox chkIgnoreWarnings =
        new JCheckBox("Ignore these warnings for the current session");
    private final JCheckBox chkDetails = new JCheckBox("Show Details");
    private final JSplitPane splitCenter = new JSplitPane(JSplitPane.VERTICAL_SPLIT, true);
    private final JSplitPane splitBottom = new JSplitPane(JSplitPane.VERTICAL_SPLIT, true);
    private final JPanel stacktracePanel = new JPanel(new BorderLayout());

    /**
     * flag to switch between dialog for warnings and critical issues where parsing is aborted. In
     * the latter case only a single exception is show, which can also not be ignored
     */
    private final boolean critical;

    /**
     * Reacts to selection events to the "Show details" checkbox (fold/unfold stacktrace). Performs
     * some calculations to make the dialog only expand/collapse the stacktrace panel, but keep the
     * rest of the dialog looking the same as before.
     */
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
    };

    public IssueDialog(Window owner, String title, Set<PositionedIssueString> issues,
            boolean critical) {
        this(owner, title, critical ? CRITICAL_ISSUE : NON_CRITICAL_ISSUE, issues, critical, null);
    }

    /**
     * Create an issue dialog with the given title and description.
     *
     * @param owner parent window
     * @param title window title
     * @param description description to show
     * @param issues the issues
     */
    public IssueDialog(Window owner, String title, String description,
            Set<PositionedIssueString> issues) {
        this(owner, title, description, issues, false, null);
    }

    /**
     * Escapes special HTML chars the Strings of the warning messages and decorates weblinks such
     * that they are clickable.
     *
     * @param warnings the warnings to decorate
     * @return the list of decorated and escaped (otherwise unchanged) warnings
     */
    private static List<PositionedIssueString> decorateHTML(Set<PositionedIssueString> warnings) {
        return warnings.stream().map(pis -> {
            Matcher m = HTTP_REGEX.matcher(pis.text);

            StringBuilder sb = new StringBuilder();
            int start = 0;
            while (m.find()) {
                // escape special HTML chars (not in link!)
                String notMatched = pis.text.substring(start, m.start());
                String escaped = LogicPrinter.escapeHTML(notMatched, true);

                // decorate link with anchor tag
                String repl = "<a href=\"" + m.group() + "\">" + m.group() + "</a>";
                sb.append(escaped);
                sb.append(repl);
                start = m.end();
            }
            // there may be a tail which has to be escaped as well ...
            String tail = pis.text.substring(start);
            String escapedTail = LogicPrinter.escapeHTML(tail, true);
            sb.append(escapedTail);

            return new PositionedIssueString(sb.toString(), pis.getLocation(),
                pis.getAdditionalInfo());
        }).collect(Collectors.toList());
    }

    /**
     * Construct a new issue dialog based on the title, the warnings to show and the exception to
     * show.
     *
     * @param owner parent window
     * @param title dialog title
     * @param warnings warnings to show
     * @param critical whether the issue is critical
     * @param throwable exception to show (may be null)
     */
    IssueDialog(Window owner, String title, Set<PositionedIssueString> warnings,
            boolean critical, Throwable throwable) {
        this(owner, title, critical ? CRITICAL_ISSUE : NON_CRITICAL_ISSUE, warnings, critical,
            throwable);
    }

    /**
     * Construct a new issue dialog given the title, description, warnings and exception.
     *
     * @param owner parent window
     * @param title dialog title
     * @param head description
     * @param warnings warnings to show
     * @param critical criticality of the issue
     * @param throwable exception to show (may be null)
     */
    IssueDialog(Window owner, String title, String head, Set<PositionedIssueString> warnings,
            boolean critical, Throwable throwable) {
        super(owner, title, ModalityType.APPLICATION_MODAL);

        this.throwable = throwable;
        this.critical = critical;

        setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        this.warnings = decorateHTML(warnings);
        this.warnings.sort(Comparator.comparing(o -> o.location));

        setLayout(new BorderLayout());

        ///////// component overview (more indention means deeper nested):
        // label
        // scrWarnings
        // listWarnings
        // ----splitCenter
        // sourcePanel
        // locPanel: fTextField lTextField cTextField
        // scrPreview: nowrap: txtSource
        // pSouth
        // chkIgnoreWarnings
        // pButtons: btnOK btnEditFile chkDetails
        // ----splitBottom
        // stacktracePanel
        // stTextArea

        // set descriptive text in top label
        JLabel label = new JLabel(head);
        label.setBorder(BorderFactory.createEmptyBorder(5, 5, 2, 5));
        add(label, BorderLayout.NORTH);

        Font font = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
        if (font == null) {
            // make sure a monospaced font is used
            font = new Font(Font.MONOSPACED, Font.PLAIN, 12);
        }

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
        splitBottom.addPropertyChangeListener(JSplitPane.DIVIDER_LOCATION_PROPERTY, e -> {
            // temporarily remove item listener to prevent infinite loop
            chkDetails.removeItemListener(detailsBoxListener);
            int newLoc = (int) e.getNewValue();
            chkDetails.setSelected(newLoc < splitBottom.getMaximumDividerLocation());
            chkDetails.addItemListener(detailsBoxListener);
        });

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
        listWarnings
                .addListSelectionListener(e -> updateStackTrace(listWarnings.getSelectedValue()));
        // enable/disable "open file" and "show details"
        listWarnings.addListSelectionListener(
            e -> btnEditFile.setEnabled(listWarnings.getSelectedValue().hasFilename()));
        listWarnings.addListSelectionListener(e -> {
            if (listWarnings.getSelectedValue().getAdditionalInfo().isEmpty()) {
                chkDetails.setSelected(false);
                chkDetails.setEnabled(false);
                /*
                 * disable the bottom split and hide the divider (we can not use setEnabled(false)
                 * on the splitpane because this has side effects on some children!)
                 */
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

        // react to mouse clicks on links by opening the url in the systems default browser
        listWarnings.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                int row = listWarnings.locationToIndex(e.getPoint());
                ListCellRenderer<? super PositionedIssueString> renderer =
                    listWarnings.getCellRenderer();
                PositionedIssueString value = listWarnings.getModel().getElementAt(row);
                JTextPane textPane = (JTextPane) renderer.getListCellRendererComponent(listWarnings,
                    value, row, false, false);
                // this line is very important, otherwise textPane would have a size of 0x0!!!
                textPane.setBounds(listWarnings.getCellBounds(row, row));
                Rectangle cellRect = listWarnings.getCellBounds(row, row);
                int x = e.getX() - cellRect.x;
                int y = e.getY() - cellRect.y;

                MouseEvent translated = new MouseEvent(textPane, e.getID(), e.getWhen(),
                    e.getModifiersEx(), x, y, e.getClickCount(), false);

                Element elem = getHyperlinkElement(translated);
                if (elem != null) {
                    Object attribute = elem.getAttributes().getAttribute(HTML.Tag.A);
                    if (attribute instanceof AttributeSet) {
                        AttributeSet set = (AttributeSet) attribute;
                        String href = (String) set.getAttribute(HTML.Attribute.HREF);
                        if (href != null) {
                            try {
                                textPane.fireHyperlinkUpdate(new HyperlinkEvent(textPane,
                                    HyperlinkEvent.EventType.ACTIVATED, new URL(href)));
                            } catch (MalformedURLException exc) {
                                LOGGER.warn("Failed to update hyperlink", exc);
                            }
                        }
                    }
                }
            }
        });

        // react to hovering over links by changing the cursor to hand
        listWarnings.addMouseMotionListener(new MouseMotionAdapter() {
            /** ensures that the cursor is only set once when entered/exited */
            boolean entered = false;

            @Override
            public void mouseMoved(MouseEvent e) {
                int row = listWarnings.locationToIndex(e.getPoint());
                ListCellRenderer<? super PositionedIssueString> renderer =
                    listWarnings.getCellRenderer();
                PositionedIssueString value = listWarnings.getModel().getElementAt(row);
                JTextPane textPane = (JTextPane) renderer.getListCellRendererComponent(listWarnings,
                    value, row, false, false);
                // this line is very important, otherwise textPane would have a size of 0x0!!!
                textPane.setBounds(listWarnings.getCellBounds(row, row));
                Rectangle cellRect = listWarnings.getCellBounds(row, row);
                int x = e.getX() - cellRect.x;
                int y = e.getY() - cellRect.y;

                MouseEvent translated = new MouseEvent(textPane, e.getID(), e.getWhen(),
                    e.getModifiersEx(), x, y, e.getClickCount(), false);

                Element elem = getHyperlinkElement(translated);
                if (elem != null) {
                    Object attribute = elem.getAttributes().getAttribute(HTML.Tag.A);
                    if (attribute instanceof AttributeSet) {
                        AttributeSet set = (AttributeSet) attribute;
                        String href = (String) set.getAttribute(HTML.Attribute.HREF);
                        if (href != null && !entered) {
                            entered = true;
                            listWarnings.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
                        }
                    }
                } else if (entered) {
                    entered = false;
                    listWarnings.setCursor(Cursor.getDefaultCursor());
                }
            }
        });

        listWarnings.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        listWarnings.setCellRenderer(new PositionedStringListRenderer());
        listWarnings.setSelectedIndex(0);
        listWarnings.setEnabled(true);
        listWarnings.setFocusable(true);
        listWarnings.setFont(font);

        JScrollPane scrWarnings;
        if (this.warnings.size() == 1) {
            // In the special case with a single warning/error, a textpane is shown instead of the
            // list. Note that for simplicity, the list is still initialized.
            JTextPane issueTextPane = new JTextPane();
            issueTextPane.setEditable(false);
            // this is needed to have the font settings respected when using html content type:
            issueTextPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, Boolean.TRUE);
            issueTextPane.setFont(font);
            issueTextPane.setContentType("text/html");
            issueTextPane.addHyperlinkListener(hle -> {
                if (hle.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
                    try {
                        Desktop.getDesktop().browse(hle.getURL().toURI());
                    } catch (Exception ex) {
                        LOGGER.warn("Failed to browse", ex);
                    }
                }
            });
            PositionedString value = this.warnings.get(0);
            issueTextPane.setText(value.text);
            scrWarnings = new JScrollPane(issueTextPane);
            // ensure that the start of the error message is visible
            issueTextPane.setCaretPosition(0);
        } else {
            scrWarnings = new JScrollPane(listWarnings);
        }
        return scrWarnings;
    }

    /**
     * Gets the hyper link element (i.e., the anchor tag of the HTMLDocument) the mouse cursor
     * currently points to.
     *
     * @param event the mouse event, needed to get the position of the cursor
     * @return the corresponding tag element or null if the mouse does not currently point to one
     */
    private static Element getHyperlinkElement(MouseEvent event) {
        JEditorPane editor = (JEditorPane) event.getSource();
        int pos = editor.getUI().viewToModel(editor, event.getPoint());
        if (pos >= 0 && editor.getDocument() instanceof HTMLDocument) {
            HTMLDocument hdoc = (HTMLDocument) editor.getDocument();
            Element elem = hdoc.getCharacterElement(pos);
            if (elem.getAttributes().getAttribute(HTML.Tag.A) != null) {
                return elem;
            }
        }
        return null;
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
        Dimension buttonDim = new Dimension(100, 29);
        btnOK.setPreferredSize(buttonDim);
        btnOK.setMinimumSize(buttonDim);
        final JButton btnSendFeedback = new JButton(new SendFeedbackAction(this, throwable));
        Dimension feedbackBtnDim =
            new Dimension(btnSendFeedback.getPreferredSize().width, buttonDim.height);
        btnSendFeedback.setMinimumSize(feedbackBtnDim);
        btnSendFeedback.setPreferredSize(feedbackBtnDim);

        Box pSouth = new Box(BoxLayout.Y_AXIS);
        JPanel pButtons = new JPanel(new FlowLayout(FlowLayout.CENTER));
        pButtons.add(btnOK);
        pButtons.add(btnEditFile);
        pButtons.add(btnSendFeedback);
        pButtons.add(chkDetails);

        chkDetails.addItemListener(detailsBoxListener);

        EditSourceFileAction action = new EditSourceFileAction(this, throwable);
        btnEditFile.setAction(action);

        GuiUtilities.attachClickOnEscListener(btnOK);

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

    /**
     * Shows the dialog with a single exception. The stacktrace is extracted and can optionally be
     * shown in the dialog.
     * Important: make sure to also log the exception before showing the dialog!
     *
     * @param parent the parent of the dialog (will be blocked)
     * @param exception the exception to display
     */
    public static void showExceptionDialog(Window parent, Throwable exception) {
        // make sure UI is usable after any exception
        MainWindow.getInstance().getMediator().startInterface(true);

        Set<PositionedIssueString> msg = Collections.singleton(extractMessage(exception));
        IssueDialog dlg = new IssueDialog(parent, "Parser Error", msg, true, exception);
        dlg.setVisible(true);
        dlg.dispose();
    }

    /**
     * Shows the dialog of a set of (non-critical) parser warnings.
     *
     * @param parent the parent of the dialog (will be blocked)
     * @param warnings the set of warnings, will be sorted by file when displaying
     */
    public static void showWarningsIfNecessary(Window parent,
            ImmutableSet<PositionedString> warnings) {
        Set<PositionedString> warn = warnings.toSet();
        warn.removeAll(ignoredWarnings);
        // do not show warnings dialog if all warnings are ignored
        if (!warn.isEmpty()) {
            // ensure that each warning has at least an empty additionalInfo
            Set<PositionedIssueString> issues = warnings.stream()
                    .map(o -> o instanceof PositionedIssueString ? (PositionedIssueString) o
                            : new PositionedIssueString(o, ""))
                    .collect(Collectors.toSet());

            IssueDialog dialog =
                new IssueDialog(parent, SLEnvInput.getLanguage() + " warning(s)", issues, false);
            dialog.setVisible(true);
            dialog.dispose();
        }
    }

    /**
     * Extracts message, position, and stracktrace from the given exception. To be successful, the
     * exception must have a location (see {@link ExceptionTools#getLocation(Throwable)}).
     *
     * @param exception the exception to extract the data from
     * @return a new PositionedIssueString created from the data
     */
    private static PositionedIssueString extractMessage(Throwable exception) {
        try (StringWriter sw = new StringWriter(); PrintWriter pw = new PrintWriter(sw)) {
            exception.printStackTrace(pw);
            String message = exception.getMessage();
            String info = sw.toString();

            // also add message of the cause to the string if available
            if (exception.getCause() != null) {
                String causeMessage = exception.getCause().getMessage();
                message = message == null ? causeMessage
                        : String.format("%s%n%nCaused by: %s", message,
                            exception.getCause().toString());
            }

            URI resourceLocation = null;
            Position pos = Position.UNDEFINED;
            Optional<Location> location = ExceptionTools.getLocation(exception);
            if (location.isPresent()) {
                var loc = location.get();
                if (!loc.getPosition().isNegative()) {
                    pos = loc.getPosition();
                }
                if (loc.getFileURI().isPresent()) {
                    resourceLocation = loc.getFileURI().get();
                }
            }
            return new PositionedIssueString(message == null ? exception.toString() : message,
                new Location(resourceLocation, pos), info);
        } catch (IOException e) {
            // We must not suppress the dialog here -> catch and print only to debug stream
            LOGGER.debug("Creating a Location failed for {}", exception, e);
        }
        return new PositionedIssueString("Constructing the error message failed!");
    }

    private void accept() {
        if (!critical && chkIgnoreWarnings.isSelected()) {
            ignoredWarnings.addAll(warnings);
        }
        setVisible(false);
    }

    private void updatePreview(PositionedIssueString issue) {
        // update text fields with position information
        Location location = issue.getLocation();
        Position pos = location.getPosition();
        cTextField.setText("Column: " + pos.column());
        lTextField.setText("Line: " + pos.line());

        btnEditFile.setEnabled(pos != Position.UNDEFINED);

        if (location.getFileURI().isEmpty()) {
            fTextField.setVisible(false);
            txtSource.setText("[SOURCE COULD NOT BE LOADED]");
        } else {
            URI uri = location.getFileURI().get();
            if (uri.getScheme() == null) {
                uri = URI.create("file:" + uri.getPath());
            }
            fTextField.setText("URL: " + uri);
            fTextField.setVisible(true);

            try {
                URI finalUri = uri;
                String source = StringUtil.replaceNewlines(
                    fileContentsCache.computeIfAbsent(uri, fn -> {
                        try {
                            return IOUtil.readFrom(finalUri).orElseThrow();
                        } catch (IOException e) {
                            LOGGER.debug("Unknown IOException!", e);
                            return "[SOURCE COULD NOT BE LOADED]\n" + e.getMessage();
                        }
                    }), "\n");

                if (isJava(uri.getPath())) {
                    showJavaSourceCode(source);
                } else {
                    txtSource.setText(source);
                }
                DefaultHighlighter dh = new DefaultHighlighter();
                txtSource.setHighlighter(dh);
                addHighlights(dh, uri);

                // ensure that the currently selected problem is shown in view
                int offset = pos.isNegative() ? 0 : getOffsetFromLineColumn(source, pos);
                txtSource.setCaretPosition(offset);
            } catch (Exception e) {
                LOGGER.warn("Failed to update preview", e);
            }
        }
        validate();
    }

    private void updateStackTrace(PositionedIssueString issue) {
        txtStacktrace.setText(issue.getAdditionalInfo());
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

    private void addHighlights(DefaultHighlighter dh, URI url) {
        warnings.stream().filter(ps -> ps.getLocation().getFileURI().equals(Optional.of(url)))
                .forEach(ps -> addHighlights(dh, ps));
    }

    private void addHighlights(DefaultHighlighter dh, PositionedString ps) {
        // if we have no position there is no highlight
        Position pos = ps.getLocation().getPosition();
        if (pos.isNegative()) {
            return;
        }
        String source = txtSource.getText();
        int offset = getOffsetFromLineColumn(source, pos);
        int end = offset;
        while (end < source.length() && !Character.isWhitespace(source.charAt(end))) {
            end++;
        }
        try {
            if (critical) {
                dh.addHighlight(offset, end, new SquigglyUnderlinePainter(Color.RED, 2, 1f));
            } else {
                dh.addHighlight(offset, end, new SquigglyUnderlinePainter(Color.ORANGE, 2, 1f));
            }
        } catch (BadLocationException ignore) {
            // ignore
        }
    }

    private boolean isJava(String fileName) {
        return fileName.endsWith(".java");
    }

    public static int getOffsetFromLineColumn(String source, Position pos) {
        // Position has 1-based line and column, we need them 0-based
        return getOffsetFromLineColumn(source, pos.line() - 1, pos.column() - 1);
    }

    private static int getOffsetFromLineColumn(String source, int line, int column) {
        if (line < 0) {
            throw new IllegalArgumentException();
        }
        if (column < 0) {
            throw new IllegalArgumentException();
        }

        int pos = 0;
        for (; pos < source.length() && line > 0; ++pos) {
            if (source.charAt(pos) == '\n') {
                --line;
            }
        }
        if (line == 0) {
            return Math.min(pos + column, source.length());
        }

        // Best effort, don't throw here
        return 0;
    }

    private static class PositionedStringListRenderer
            implements ListCellRenderer<PositionedString> {
        private final JTextPane textPane = new JTextPane();

        PositionedStringListRenderer() {
            // react to hyperlink events by opening them in default browser
            textPane.addHyperlinkListener(hle -> {
                if (hle.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
                    try {
                        Desktop.getDesktop().browse(hle.getURL().toURI());
                    } catch (Exception ex) {
                        LOGGER.warn("Failed to browse", ex);
                    }
                }
            });
        }

        @Override
        public Component getListCellRendererComponent(JList<? extends PositionedString> list,
                PositionedString value, int index, boolean isSelected, boolean cellHasFocus) {
            textPane.setContentType("text/html");
            textPane.setText(value.text);
            // use a compound border to have both: a bit more space and small lines between the rows
            textPane.setBorder(BorderFactory.createCompoundBorder(
                BorderFactory.createMatteBorder(0, 0, 1, 0, Color.LIGHT_GRAY),
                BorderFactory.createEmptyBorder(5, 5, 5, 5)));
            if (isSelected) {
                // for some reason, this copy is needed to get correct colors
                Color bg = new Color(list.getSelectionBackground().getRGB());
                Color fg = new Color(list.getSelectionForeground().getRGB());
                textPane.setBackground(bg);
                textPane.setForeground(fg);
            } else {
                textPane.setBackground(list.getBackground());
                textPane.setForeground(list.getForeground());
            }

            textPane.setEnabled(true);
            textPane.setEditable(false);
            // this is needed to have the font settings respected when using html content type:
            textPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, Boolean.TRUE);
            textPane.setFont(list.getFont());
            return textPane;
        }
    }
}
