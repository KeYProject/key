package de.uka.ilkd.key.gui.sourceview;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Point;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionListener;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextPane;
import javax.swing.JViewport;
import javax.swing.SwingConstants;
import javax.swing.UIManager;
import javax.swing.border.BevelBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.Document;
import javax.swing.text.Highlighter;
import javax.swing.text.Highlighter.HighlightPainter;
import javax.swing.text.SimpleAttributeSet;

import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.nodeviews.CurrentGoalView;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.Pair;

/**
 * This class is responsible for showing the source code and visualizing the symbolic execution
 * path of the currently selected node. This is done by adding tabs containing the source code and
 * highlighting the lines which were symbolically executed in the path from the root node down to
 * the current node.
 * In addition, by clicking on such a highlighted line the user can jump to the first node in the
 * proof tree where a statement from this line is symbolically executed.
 *
 * Editing the source code in the tabs is currently not implemented
 * (not supported by {@link JavaDocument}).
 *
 * @author Wolfram Pfeifer
 * @author lanzinger
 */
public final class SourceView extends JComponent {

    /* TODO: make proof independent, move sources and hashes to proof.services.JavaModel or similar
     * There is still a consistency problem here if the proof is change: In that case the code is
     * silently reloaded from the (possibly changed) file. This will be solved in future work.
     * Corresponding feature request:
     */

    private static final long serialVersionUID = -94424677425561025L;

    /**
     * the only instance of this singleton
     */
    private static SourceView instance;

    /**
     * ToolTip for the textPanes containing the source code.
     */
    private static final String TEXTPANE_TOOLTIP = "Click on a highlighted line to jump to the "
            + "most recent occurrence of this line in symbolic execution.";

    /**
     * String to display in an empty source code textPane.
     */
    private static final String NO_SOURCE = "No source loaded";

    /**
     * Indicates how many spaces are inserted instead of one tab (used in source code window).
     */
    private static final int TAB_SIZE = 4;

    /**
     * The color of normal highlights in source code (light green).
     */
    private static final Color NORMAL_HIGHLIGHT_COLOR = new Color(194, 245, 194);

    /**
     * The color of the most recent highlight in source code (green).
     */
    private static final Color MOST_RECENT_HIGHLIGHT_COLOR = new Color(57, 210, 81);

    /**
     * The main window of KeY (needed to get the mediator).
     */
    private final MainWindow mainWindow;

    /**
     * Maps every file to a tab.
     */
    private final Map<String, Tab> tabs = new HashMap<>();

    /**
     * Pane containing the tabs.
     */
    private final TabbedPane tabPane = new TabbedPane();

    /**
     * Currently selected file.
     */
    private String selectedFile = null;

    /**
     * The status bar for displaying information about the current proof branch.
     */
    private final JLabel sourceStatusBar;

    /**
     * Lines to highlight (contains all highlights of the current proof) and corresponding Nodes.
     */
    private LinkedList<Pair<Node, PositionInfo>> lines;

    Set<Highlight> symbExHighlights = new HashSet<>();

    /**
     * Creates a new JComponent with the given MainWindow and adds change listeners.
     * @param mainWindow the MainWindow of the GUI
     */
    private SourceView(MainWindow mainWindow) {
        super();
        this.mainWindow = mainWindow;

        sourceStatusBar = new JLabel();
        tabPane.setBorder(new TitledBorder("No source loaded"));

        tabPane.addChangeListener(new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                selectedFile = tabPane.getSelectedTab() == null
                        ? null
                        : tabPane.getSelectedTab().file.getAbsolutePath();
            }
        });

        // set the same style as the main status line:
        sourceStatusBar.setBorder(new BevelBorder(BevelBorder.LOWERED));
        sourceStatusBar.setBackground(Color.gray);

        // add extra height to make the status bar more noticeable
        sourceStatusBar.setPreferredSize(
                new Dimension(0, getFontMetrics(sourceStatusBar.getFont()).getHeight() + 6));
        sourceStatusBar.setHorizontalAlignment(SwingConstants.CENTER);

        setLayout(new BorderLayout());
        add(tabPane, BorderLayout.CENTER);
        add(sourceStatusBar, BorderLayout.SOUTH);

        // react to font changes
        Config.DEFAULT.addConfigChangeListener(new ConfigChangeListener() {
            @Override
            public void configChanged(ConfigChangeEvent e) {
                for (Tab tab : tabs.values()) {
                    tab.textPane.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
                }
            }
        });

        // add a listener for changes in the proof tree
        mainWindow.getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                if (!mainWindow.getMediator().isInAutoMode()) {
                    updateGUI();
                }
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                clear();
                updateGUI();
            }
        });
    }

    /**
     * <p> Creates a new highlight. </p>
     *
     * <p> If the are multiple highlight for a given line, the highlight with the highest level
     *  is used. </p>
     *
     * <p> The highlights added by the {@code SourceView} itself have level {@code 0},
     *  except for the highlight that appears when the user moves the mouse over a line,
     *  which has level {@code Integer.maxValue() - 1}. </p>
     *
     * @param fileName the name of the file in which to create the highlight.
     * @param line the line to highlight.
     * @param color the color to use for the highlight.
     * @param level the level of the highlight.
     * @return the highlight.
     *
     * @throws BadLocationException if the line number is invalid.
     * @throws IOException if the file cannot be read.
     */
    public Highlight addHighlight(String fileName, int line, Color color, int level)
            throws BadLocationException, IOException {
        openFile(fileName);

        Tab tab = tabs.get(fileName);

        if (line < 0 || line >= tab.lineInformation.length) {
            throw new BadLocationException("Not a valid line number for " + fileName, line);
        }

        if (!tab.highlights.containsKey(line)) {
            tab.highlights.put(line, new TreeSet<>());
        }

        SortedSet<Highlight> highlights = tab.highlights.get(line);

        Highlight highlight = new Highlight(fileName, line, color, level);
        highlights.add(highlight);

        if (highlight.compareTo(highlights.last()) >= 0) {
            tab.removeHighlights(line);
            tab.applyHighlights(line);
        }

        return highlight;
    }

    /**
     * Moves an existing highlight to another line.
     *
     * @param highlight the highlight to change.
     * @param newLine the line to move the highlight to.
     *
     * @throws BadLocationException if the line number is invalid.
     * @throws IOException if the file cannot be read.
     */
    public void changeHighlight(Highlight highlight, int newLine)
            throws BadLocationException, IOException {
        String fileName = highlight.getFileName();
        int oldLine = highlight.getLine();

        Tab tab = tabs.get(fileName);

        if (tab == null
                || !tab.highlights.containsKey(oldLine)
                || !tab.highlights.get(oldLine).contains(highlight)) {
            throw new IllegalArgumentException("highlight");
        }

        tab.removeHighlights(oldLine);
        tab.highlights.get(oldLine).remove(highlight);
        tab.applyHighlights(oldLine);

        highlight.line = newLine;
        highlight.setTag(null);

        if (!tab.highlights.containsKey(newLine)) {
            tab.highlights.put(newLine, new TreeSet<>());
        }

        tab.highlights.get(newLine).add(highlight);

        if (highlight.compareTo(tab.highlights.get(newLine).last()) >= 0) {
            tab.applyHighlights(newLine);
        }
    }

    /**
     * Removes a highlight.
     *
     * @param highlight the highlight to remove.
     * @return {@code true} iff
     *      this {@code SourceView} previously contained the specified highlight.
     */
    public boolean removeHighlight(Highlight highlight) {
        Tab tab = tabs.get(highlight.getFileName());

        if (tab == null) {
            return false;
        }

        tab.removeHighlights(highlight.getLine());

        boolean result = tab.highlights.containsKey(highlight.getLine())
                && tab.highlights.get(highlight.getLine()).remove(highlight);
        highlight.setTag(null);

        try {
            tab.applyHighlights(highlight.getLine());
        } catch (BadLocationException | IOException e) {
            // The locations of the highlights have already been checked
            // in addHighlight & changeHighlight, so no error can occur here.
            throw new AssertionError();
        }

        return result;
    }

    /**
     * Adds an additional tab for the specified file.
     *
     * @param filename the name of the file to open.
     */
    public void openFile(String filename) {
        Set<String> set = new HashSet<>();
        set.add(filename);
        openFiles(set);
    }

    /**
     * Adds additional tabs for the specified files.
     *
     * @param filenames the names of the files to open.
     */
    public void openFiles(Set<String> filenames) {
        boolean updateNecessary = false;

        for (String filename : filenames) {
            if (addFile(filename)) {
                updateNecessary = true;
            }
        }

        if (updateNecessary) {
            updateGUI();
        }
    }

    /**
     * Calculates the range of actual text (not whitespace) in the line containing the given
     * position.
     * @param textPane the JTextPane with the text
     * @param pos the position to check
     * @return the range of text (may be empty if there is just whitespace in the line)
     */
    private static Range calculateLineRange(JTextPane textPane, int pos) {
        Document doc = textPane.getDocument();
        String text = "";
        try {
            text = doc.getText(0, doc.getLength());
        } catch (BadLocationException e) {
            Debug.out(e);
        }

        // find line end
        int end = text.indexOf('\n', pos);
        end = end == -1 ? text.length() : end;      // last line?

        // find line start
        int start = text.lastIndexOf('\n', pos - 1);          // TODO: different line endings?
        start = start == -1 ? 0 : start;            // first line?

        // ignore whitespace at the beginning of the line
        while (start < text.length() && start < end && Character.isWhitespace(text.charAt(start))) {
            start++;
        }

        return new Range(start, end);
    }

    /**
     * Replaces each tab in the given String by TAB_SIZE spaces.
     * @param s the String to replace
     * @return the resulting String (without tabs)
     */
    private static String replaceTabs(String s) {
        // fill a new array with the specified amount of spaces
        char[] rep = new char[TAB_SIZE];
        for (int i = 0; i < rep.length; i++) {
            rep[i] = ' ';
        }
        return s.replace("\t", new String(rep));
    }

    private boolean isSelected(Tab tab) {
        return Objects.equals(selectedFile, tab.getFileName());
    }

    /**
     * Adds all files in {@link #lines}.
     */
    private void addFiles() {
        for (Pair<Node, PositionInfo> p : lines) {
            PositionInfo l = p.second;
            addFile(l.getFileName());
        }
    }

    /**
     * Adds a file to this source view.
     *
     * @param filename the name of the file to add.
     * @return {@code true} if this source view did not already contain the file.
     */
    private boolean addFile(String fileName) {
        File file = new File(fileName);

        if (file.exists() && !tabs.containsKey(fileName)) {
            new Tab(file);
            return true;
        }

        return false;
    }

    /**
     * Returns the singleton instance of the SourceView.
     * @param mainWindow KeY's main window
     * @return the component responsible for showing source code and symbolic execution information
     */
    public static SourceView getSourceView(MainWindow mainWindow) {
        if (instance == null) {
            instance = new SourceView(mainWindow);
        }
        return instance;
    }

    private void clear() {
        lines = null;
        tabs.clear();
        tabPane.removeAll();
    }

    /**
     * Performs an update of the GUI:
     * <ul>
     *      <li>updates the TabbedPane with the source files used</li>
     *      <li>highlights the symbolically executed lines</li>
     *      <li>updates the source status bar of the main window with information about the current
     *          branch</li>
     * </ul>
     */
    private void updateGUI() {
        Node currentNode = mainWindow.getMediator().getSelectedNode();

        if (currentNode != null) {
            // get PositionInfo of all symbEx nodes
            lines = constructLinesSet(currentNode);
            if (lines == null) {
                tabPane.setBorder(new TitledBorder(NO_SOURCE));
                sourceStatusBar.setText(NO_SOURCE);
                return;
            }

            addFiles();
        }

        tabs.values().forEach(Tab::resetHighlights);

        if (tabPane.getTabCount() > 0) {
            tabPane.setBorder(new EmptyBorder(0, 0, 0, 0));

            // activate the tab with the most recent file
            PositionInfo p = lines.isEmpty() ? null : lines.getFirst().second;
            if (p != null) {
                File f = tabs.get(p.getFileName()).file;
                if (f != null) {
                    String s = f.getName();
                    for (int i = 0; i < tabPane.getTabCount(); i++) {
                        if (tabPane.getTitleAt(i).equals(s)) {
                            tabPane.setSelectedIndex(i);

                            // scroll to most recent highlight
                            int line = lines.getFirst().second.getEndPosition().getLine();
                            scrollNestedTextPaneToLine(tabPane.getComponent(i), line, f);
                        }
                    }
                }
            }

            // set the path information in the status bar
            sourceStatusBar.setText(collectPathInformation(currentNode));
        } else {
            tabPane.setBorder(new TitledBorder(NO_SOURCE));
            sourceStatusBar.setText(NO_SOURCE);
        }
    }

    /**
     * Looks for a nested JTextPane in the component of the JTabbedPane.
     * If it exists, JTextPane is scrolled to the given line.
     * @param comp the component of a JTabbedPane
     * @param line the line to scroll to
     * @param f the file of the JTextPane
     */
    private static void scrollNestedTextPaneToLine(Component comp, int line, File f) {
        if (comp instanceof JScrollPane) {
            JScrollPane sp = (JScrollPane)comp;
            if (sp.getComponent(0) instanceof JViewport) {
                JViewport vp = (JViewport)sp.getComponent(0);
                if (vp.getComponent(0) instanceof JPanel) {
                    JPanel panel = (JPanel)vp.getComponent(0);
                    if (panel.getComponent(0) instanceof JTextPane) {
                        JTextPane tp = (JTextPane)panel.getComponent(0);
                        try {
                            String original = IOUtil.readFrom(f);
                            String source = replaceTabs(original);  // replace all tabs by spaces

                            /* use input stream here to compute line information of the string with
                             * replaced tabs
                             */
                            InputStream inStream = new ByteArrayInputStream(source.getBytes());
                            LineInformation[] li = IOUtil.computeLineInformation(inStream);
                            int offs = li[line].getOffset();
                            tp.setCaretPosition(offs);
                        } catch (IOException e) {
                            Debug.out(e);
                        }
                    }
                }
            }
        }
    }

    /**
     * Collects the set of lines to highlight starting from the given node in the proof tree.
     * @param cur the given node
     * @return a linked list of pairs of PositionInfo objects containing the start and end
     * positions for the highlighting and Nodes.
     */
    private static LinkedList<Pair<Node, PositionInfo>> constructLinesSet(Node cur) {
        LinkedList<Pair<Node, PositionInfo>> list = new LinkedList<Pair<Node, PositionInfo>>();

        if (cur == null) {
            return null;
        }

        do {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                if (activeStatement instanceof SourceElement) {
                    PositionInfo pos = joinPositionsRec(activeStatement);

                    // we are only interested in well defined PositionInfo objects with a file name
                    if (pos != null && !pos.equals(PositionInfo.UNDEFINED) && pos.startEndValid()
                            && pos.getFileName() != null) {
                        list.addLast(new Pair<Node, PositionInfo>(cur, pos));
                    }
                }
            }
            cur = cur.parent();

        } while (cur != null);
        return list;
    }

    /**
     * Joins all PositionInfo objects of the given SourceElement and its children.
     * @param se the given SourceElement
     * @return a new PositionInfo starting at the minimum of all the contained positions and
     * ending at the maximum position
     */
    private static PositionInfo joinPositionsRec(SourceElement se) {
        if (se instanceof NonTerminalProgramElement) {
            if (se instanceof If
                    || se instanceof Then
                    || se instanceof Else) { // TODO: additional elements, e.g. code inside if
                return PositionInfo.UNDEFINED;
            }

            NonTerminalProgramElement ntpe = (NonTerminalProgramElement)se;
            PositionInfo pos = se.getPositionInfo();

            for (int i = 0; i < ntpe.getChildCount(); i++) {
                ProgramElement pe2 = ntpe.getChildAt(i);
                pos = PositionInfo.join(pos, joinPositionsRec(pe2));
            }
            return pos;
        } else {
            return se.getPositionInfo();
        }
    }

    /**
     * Collects the information from the tree to which branch the current node belongs:
     * <ul>
     *      <li>Invariant Initially Valid</li>
     *      <li>Body Preserves Invariant</li>
     *      <li>Use Case</li>
     *      <li>...</li>
     * </ul>
     * @param node the current node
     * @return a String containing the path information to display
     */
    private static String collectPathInformation(Node node) {
        while (node != null) {
            if (node.getNodeInfo() != null && node.getNodeInfo().getBranchLabel() != null) {
                String label = node.getNodeInfo().getBranchLabel();
                /* Are there other interesting labels?
                 * Please feel free to add them here. */
                if (label.equals("Invariant Initially Valid")
                        || label.equals("Invariant Preserved and Used") // for loop scope invariant
                        || label.equals("Body Preserves Invariant")
                        || label.equals("Use Case")
                        || label.equals("Show Axiom Satisfiability")
                        || label.startsWith("Pre (")                // precondition of a method
                        || label.startsWith("Exceptional Post (")   // exceptional postcondition
                        || label.startsWith("Post (")               // postcondition of a method
                        || label.contains("Normal Execution")
                        || label.contains("Null Reference")
                        || label.contains("Index Out of Bounds")) {
                    return label;
                }
            }
            node = node.parent();
        }
        // if no label was found we have to prove the postcondition
        return "Show Postcondition/Assignable";
    }



    private class TabbedPane extends JTabbedPane {

        public Tab getTabAt(int index) {
            return (Tab) getComponentAt(index);
        }

        public Tab getSelectedTab() {
            return (Tab) getSelectedComponent();
        }
    };

    private class Tab extends JScrollPane {

        /**
         * The file this tab belongs to.
         */
        private final File file;

        /**
         * The text pane containing the file's content.
         */
        private final JTextPane textPane = new JTextPane();

        private LineInformation[] lineInformation;

        /**
         * Hash of the file's contents.
         */
        private String sourceHash;

        /**
         * The file's content.
         */
        private String source;

        /**
         * This tab's index.
         *
         * @see JTabbedPane#getTabComponentAt(int)
         */
        private int index;

        /**
         * The highlight for the user's selection.
         */
        private Highlight selectionHL;

        /**
         * Maps line numbers to highlights.
         */
        private Map<Integer, SortedSet<Highlight>> highlights = new HashMap<>();

        private Tab(File file) {
            this.file = file;

            tabs.put(getFileName(), this);

            try {
                String text = IOUtil.readFrom(file);
                if (text != null && !text.isEmpty()) {
                    sourceHash = IOUtil.computeMD5(file);
                    source = replaceTabs(text);
                }
            } catch (IOException e) {
                Debug.out("Unknown IOException!", e);
            }

            // We use the same font as in SequentView for consistency.
            textPane.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
            textPane.setToolTipText(TEXTPANE_TOOLTIP);
            textPane.setEditable(false);

            // compare stored hash with a newly created
            //String origHash = hashes.get(entry.getKey());
            //String curHash = IOUtil.computeMD5(entry.getValue());
            //if (!origHash.equals(curHash)) {
            // TODO: consistency problem, see comment in line 128
            //}

            // set lineInformation
            try {
                InputStream inStream = new ByteArrayInputStream(source.getBytes());
                lineInformation = IOUtil.computeLineInformation(inStream);
            } catch (IOException e) {
                Debug.out("Error while computing line information from " + file, e);
            }

            // insert source code into text pane
            try {
                JavaDocument doc = new JavaDocument();
                textPane.setDocument(doc);
                doc.insertString(0, source, new SimpleAttributeSet());
            } catch (BadLocationException e) {
                throw new AssertionError();
            }

            // add a listener to highlight the line currently pointed to
            try {
                selectionHL = addHighlight(
                        getFileName(),
                        1,
                        CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR,
                        Integer.MAX_VALUE - 1);

                textPane.addMouseMotionListener(new MouseMotionListener() {
                    @Override
                    public void mouseMoved(MouseEvent e) {
                        paintSelectionHighlight(e.getPoint(), selectionHL);
                    }

                    @Override
                    public void mouseDragged(MouseEvent e) { }
                });
            } catch (BadLocationException | IOException e) {
                throw new AssertionError();
            }

            textPane.addMouseListener(new TextPaneMouseAdapter(
                    textPane, lineInformation, getFileName()));

            JPanel nowrap = new JPanel(new BorderLayout());
            nowrap.add(textPane);
            setViewportView(nowrap);
            setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED);

            // increase unit increment (for faster scrolling)
            getVerticalScrollBar().setUnitIncrement(30);
            getHorizontalScrollBar().setUnitIncrement(30);

            //add Line numbers to each Scrollview
            TextLineNumber tln = new TextLineNumber(textPane, 4);
            setRowHeaderView(tln);

            // Add tab to tab pane.
            tabPane.addTab(file.getName(), this);
            int index = tabPane.indexOfComponent(this);
            tabPane.setToolTipTextAt(index, file.getAbsolutePath());

            resetHighlights();
        }

        private void resetHighlights() {
            try {
                for (int i = 0; i < lineInformation.length; ++i) {
                    removeHighlights(i);
                }

                calculateSymbExHighlights();

                for (int i = 0; i < lineInformation.length; ++i) {
                    applyHighlights(i);
                }
            } catch (IOException | BadLocationException e) {
                Debug.out(e);
            }
        }

        private String getFileName() {
            return file.getAbsolutePath();
        }

        private void removeHighlights(int line) {
            if (!isSelected(this)) {
                return;
            }

            SortedSet<Highlight> set = highlights.get(line);

            if (set == null) {
                return;
            }

            for (Highlight highlight : set) {
                if (highlight.getTag() != null) {
                    textPane.getHighlighter().removeHighlight(highlight.getTag());
                    highlight.setTag(null);
                }
            }
        }

        private void applyHighlights(int line)
                throws BadLocationException, IOException {
            if (!isSelected(this)) {
                return;
            }

            SortedSet<Highlight> set = highlights.get(line);

            if (set != null && !set.isEmpty()) {
                Highlight highlight = set.last();
                Range range = calculateLineRange(
                        textPane,
                        lineInformation[highlight.getLine() - 1].getOffset());

                highlight.setTag(textPane.getHighlighter().addHighlight(
                        range.start(),
                        range.end(),
                        new DefaultHighlightPainter(highlight.getColor())));
            }

            textPane.revalidate();
            textPane.repaint();
        }

        /**
         * Paints the highlights for symbolically executed lines. The most recently executed line is
         * highlighted with a different color.
         *
         * @throws IOException
         */
        private void calculateSymbExHighlights() throws IOException {
            for (Highlight hl : symbExHighlights) {
                removeHighlight(hl);
            }

            symbExHighlights.clear();

            try {
                for (int i = 0; i < lines.size(); i++) {
                    Pair<Node, PositionInfo> l = lines.get(i);
                    if (getFileName().equals(l.second.getFileName())) {
                        // use a different color for most recent
                        if (i == 0) {
                            symbExHighlights.add(addHighlight(
                                    getFileName(),
                                    l.second.getStartPosition().getLine() - 1,
                                    MOST_RECENT_HIGHLIGHT_COLOR,
                                    0));
                        } else {
                            symbExHighlights.add(addHighlight(
                                    getFileName(),
                                    l.second.getStartPosition().getLine() - 1,
                                    NORMAL_HIGHLIGHT_COLOR,
                                    0));
                        }
                    }
                }
            } catch (BadLocationException e) {
                Debug.out(e);
            }
        }

        private int posToLine(int pos) {
            return textPane.getDocument().getDefaultRootElement().getElementIndex(pos) + 1;
        }

        /**
         * Paints the highlight for the line where the mouse pointer currently points to.
         * @param textPane the textPane to highlight lines
         * @param p the current position of the mouse pointer
         * @param highlight the highlight to change
         *
         * @throws IOException
         */
        private void paintSelectionHighlight(Point p, Highlight highlight) {
            try {
                int line = posToLine(textPane.viewToModel(p));
                changeHighlight(highlight, line);
            } catch (BadLocationException | IOException e) {
                Debug.out(e);
            }
        }
    }

    /**
     * <p> An object of this class represents a highlight of a specific line in the
     *  {@code SourceView}. </p>
     *
     * <p>
     *  A highlight consists of the name of a file, a line in that file, a color, and a level.
     * </p>
     *
     * <p> If the are multiple highlight for a given line, the highlight with the highest level
     *  is used. </p>
     *
     * <p> The highlights added by the {@code SourceView} itself have level {@code 0},
     *  except for the highlight that appears when the user moves the mouse over a line,
     *  which has level {@code Integer.maxValue() - 1}. </p>
     *
     * @author lanzinger
     */
    public static class Highlight implements Comparable<Highlight> {

        private static final Map<Highlight, Object> tags = new HashMap<>();

        private int level;
        private Color color;
        private String fileName;
        private int line;

        private Highlight(String fileName, int line, Color color, int level) {
            this.level = level;
            this.color = color;
            this.fileName = fileName;
            this.line = line;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((color == null) ? 0 : color.hashCode());
            result = prime * result + ((fileName == null) ? 0 : fileName.hashCode());
            result = prime * result + level;
            result = prime * result + line;
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            Highlight other = (Highlight) obj;
            if (color == null) {
                if (other.color != null) {
                    return false;
                }
            } else if (!color.equals(other.color)) {
                return false;
            }
            if (fileName == null) {
                if (other.fileName != null) {
                    return false;
                }
            } else if (!fileName.equals(other.fileName)) {
                return false;
            }
            if (level != other.level) {
                return false;
            }
            if (line != other.line) {
                return false;
            }
            return true;
        }

        @Override
        public int compareTo(Highlight other) {
            int result = fileName.compareTo(other.fileName);

            if (result == 0) {
                result = Integer.compare(line, other.line);
            }

            if (result == 0) {
                result = Integer.compare(level, other.level);
            }

            if (result == 0) {
                result = Integer.compare(color.getRGB(), other.color.getRGB());
            }

            return result;
        }

        /**
         *
         * @param tag the new tag wrapped by this object.
         *
         * @see Highlighter#addHighlight(int, int, HighlightPainter)
         * @see Highlighter#changeHighlight(Object, int, int)
         * @see Highlighter#removeHighlight(Object)
         */
        private void setTag(Object tag) {
            if (tag == null) {
                tags.remove(this);
            } else {
                tags.put(this, tag);
            }
        }

        /**
         *
         * @return the tag wrapped by this object.
         *
         * @see Highlighter#addHighlight(int, int, HighlightPainter)
         * @see Highlighter#changeHighlight(Object, int, int)
         * @see Highlighter#removeHighlight(Object)
         */
        private Object getTag() {
            return tags.get(this);
        }

        /**
         *
         * @return this highlight's level.
         */
        public int getLevel() {
            return level;
        }

        /**
         *
         * @return this highlight's color.
         */
        public Color getColor() {
            return color;
        }

        /**
         *
         * @return the file in which this highlight is used.
         */
        public String getFileName() {
            return fileName;
        }

        /**
         *
         * @return the line being highlighted.
         */
        public int getLine() {
            return line;
        }
    }

    /**
     * This listener checks if a highlighted section is clicked. If true, a jump in the proof tree
     * to the most recently created node (in the current branch) containing the highlighted
     * statement is performed.<br>
     * <b>Note:</b> No jumping down in the proof tree is possible. Implementing this would be
     * non-trivial, because it was not unique into which branch we would want to descent.
     *
     * @author Wolfram Pfeifer
     */
    private class TextPaneMouseAdapter extends MouseAdapter {
        /**
         * The precalculated start indices of the lines. Used to compute the clicked line number.
         */
        final LineInformation[] li;

        /**
         * The JTextPane containing the source code.
         */
        final JTextPane textPane;

        /**
         * The filename of the file whose content is displayed in the JTextPane.
         */
        final String filename;

        public TextPaneMouseAdapter(JTextPane textPane, LineInformation[] li,
                String filename) {
            this.textPane = textPane;
            this.li = li;
            this.filename = filename;
        }

        /**
         * Checks if the given position is within a highlight.
         * @param pos the position to check
         * @return true if highlighted and false if not
         */
        private boolean isHighlighted(int pos) {
            Tab tab = tabs.get(selectedFile);

            int line = tab.posToLine(pos);

            for (Highlight h : symbExHighlights) {
                if (line == h.line) {
                    return true;
                }
            }
            return false;
        }

        @Override
        public void mouseClicked(MouseEvent e) {
            int pos = textPane.viewToModel(e.getPoint());
            if (isHighlighted(pos)) {
                int line = 0;
                // calculate the line number
                while (line < li.length - 1) {
                    if (li[line].getOffset() <= pos && pos < li[line + 1].getOffset()) {
                        break;
                    }
                    line++;
                }
                // jump in proof tree (get corresponding node from list)
                Node n = null;
                for (Pair<Node, PositionInfo> p : lines) {
                    if (p.second.getStartPosition().getLine() == line + 1
                            && p.second.getFileName().equals(filename)) {
                        n = p.first;
                        break;
                    }
                }
                if (n != null) {
                    mainWindow.getMediator().getSelectionModel().setSelectedNode(n);
                }
            }
        }
    }
}
