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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
     * The container for the tabs containing source code.
     */
    private final JTabbedPane tabs;

    /**
     * Stores the actual textPanes of the tabs. Needed for correct updates when font (size) changes.
     */
    private final List<JTextPane> textPanes = new LinkedList<JTextPane>();

    /**
     * The status bar for displaying information about the current proof branch.
     */
    private final JLabel sourceStatusBar;

    /**
     * HashMap mapping filenames to files (of the current proof!).
     */
    private Map<String, File> files = new HashMap<String, File>();

    /**
     * List mapping tab indices to file names.
     */
    private List<String> tabFiles = new ArrayList<>();

    /**
     * Name of the currently selected file.
     */
    private String selectedFile = null;

    /**
     * The highlight for the user's selection.
     */
    private Highlight selectionHL;

    /**
     * Map mapping file names and line numbers to highlights.
     */
    private Map<Pair<String, Integer>, SortedSet<Highlight>> highlights = new HashMap<>();

    /**
     * HashMap mapping filenames to hashes of the content (files of the current proof!).
     */
    private Map<String, String> hashes = new HashMap<String, String>();

    /**
     * HashMap mapping filenames to content strings (files of the current proof!).
     */
    private Map<String, String> sources = new HashMap<String, String>();

    /**
     * The text pane containing the source code of the currently selected file.
     *
     * @see #initTextPane(Entry)
     */
    private JTextPane textPane;

    /**
     * Lines to highlight (contains all highlights of the current proof) and corresponding Nodes.
     */
    private LinkedList<Pair<Node, PositionInfo>> lines;

    /**
     * HashMap mapping filenames to line info.
     */
    private Map<String, LineInformation[]> lineInformation = new HashMap<>();

    private

    Set<Highlight> symbExHighlights = new HashSet<>();

    /**
     * Creates a new JComponent with the given MainWindow and adds change listeners.
     * @param mainWindow the MainWindow of the GUI
     */
    private SourceView(MainWindow mainWindow) {
        super();
        this.mainWindow = mainWindow;

        tabs = new JTabbedPane();
        sourceStatusBar = new JLabel();
        tabs.setBorder(new TitledBorder("No source loaded"));

        tabs.addChangeListener(new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                int idx = tabs.getSelectedIndex();
                selectedFile = idx >= 0 ? tabFiles.get(idx) : null;
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
        add(tabs, BorderLayout.CENTER);
        add(sourceStatusBar, BorderLayout.SOUTH);

        // react to font changes
        Config.DEFAULT.addConfigChangeListener(new ConfigChangeListener() {
            @Override
            public void configChanged(ConfigChangeEvent e) {
                for (JTextPane tp : textPanes) {
                    tp.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
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
                clearCaches();
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

        if (line < 0 || line >= getLineInformation(fileName).length) {
            throw new BadLocationException("Not a valid line number for " + fileName, line);
        }

        Pair<String, Integer> key = new Pair<>(fileName, line);

        if (!highlights.containsKey(key)) {
            highlights.put(key, new TreeSet<>());
        }

        Highlight highlight = new Highlight(fileName, line, color, level);
        highlights.get(key).add(highlight);

        if (highlight.compareTo(highlights.get(key).last()) >= 0) {
            removeAllHighlights(fileName, line);
            applyLastHighlight(fileName, line);
        }

        return highlight;
    }

    /**
     * Moves an existing highlight to another line.
     *
     * @param highlight the highlight to change.
     * @param line the line to move the highlight to.
     *
     * @throws BadLocationException if the line number is invalid.
     * @throws IOException if the file cannot be read.
     */
    public void changeHighlight(Highlight highlight, int line)
            throws BadLocationException, IOException {
        Pair<String, Integer> oldKey = new Pair<>(highlight.getFileName(), highlight.getLine());
        Pair<String, Integer> newKey = new Pair<>(highlight.getFileName(), line);

        if (!highlights.containsKey(oldKey) || !highlights.get(oldKey).contains(highlight)) {
            throw new IllegalArgumentException("highlight");
        }

        removeAllHighlights(highlight.getFileName(), highlight.getLine());
        highlights.get(oldKey).remove(highlight);
        applyLastHighlight(highlight.getFileName(), highlight.getLine());

        highlight.line = line;
        highlight.setTag(null);

        if (!highlights.containsKey(newKey)) {
            highlights.put(newKey, new TreeSet<>());
        }

        highlights.get(newKey).add(highlight);

        if (highlight.compareTo(highlights.get(newKey).last()) >= 0) {
            applyLastHighlight(highlight.getFileName(), line);
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
        Pair<String, Integer> key = new Pair<>(highlight.getFileName(), highlight.getLine());

        removeAllHighlights(highlight.getFileName(), highlight.getLine());

        boolean result = highlights.containsKey(key) && highlights.get(key).remove(highlight);
        highlight.setTag(null);

        try {
            applyLastHighlight(highlight.getFileName(), highlight.getLine());
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
     *
     * @return the name of the currently selected file.
     */
    public String getSelectedFileName() {
        return selectedFile;
    }

    private void removeAllHighlights(String fileName, int line) {
        if (!Objects.equals(getSelectedFileName(), fileName)) {
            return;
        }

        SortedSet<Highlight> set = highlights.get(new Pair<>(fileName, line));

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

    private void applyLastHighlight(String fileName, int line)
            throws BadLocationException, IOException {
        if (!Objects.equals(getSelectedFileName(), fileName)) {
            return;
        }

        SortedSet<Highlight> set = highlights.get(new Pair<>(fileName, line));

        if (set != null && !set.isEmpty()) {
            Highlight highlight = set.last();
            LineInformation[] li = getLineInformation(getSelectedFileName());
            Range range = calculateLineRange(textPane, li[highlight.getLine() - 1].getOffset());

            highlight.setTag(textPane.getHighlighter().addHighlight(
                    range.start(),
                    range.end(),
                    new DefaultHighlightPainter(highlight.getColor())));
        }

        textPane.revalidate();
        textPane.repaint();
    }

    private void applyHighlights(String fileName) throws IOException {
        try {
            for (int i = 0; i < getLineInformation(getSelectedFileName()).length; ++i) {
                applyLastHighlight(fileName, i);
            }
        } catch (BadLocationException e) {
            // The locations of the highlights are checked in addHighlight,
            // so no error can occur here.
            throw new AssertionError();
        }
    }

    private LineInformation[] getLineInformation(String fileName) throws IOException {
        if (!lineInformation.containsKey(fileName)) {
            String original = sources.get(fileName);
            String source = replaceTabs(original);
            InputStream inStream = new ByteArrayInputStream(source.getBytes());

            lineInformation.put(fileName, IOUtil.computeLineInformation(inStream));
        }

        return lineInformation.get(fileName);
    }

    /**
     * Paints the highlights for symbolically executed lines. The most recently executed line is
     * highlighted with a different color.
     * @param filename the name of the file for which to calculate the highlights
     *
     * @throws IOException
     */
    private void calculateSymbExHighlights(String filename) throws IOException {
        for (Highlight hl : symbExHighlights) {
            removeHighlight(hl);
        }

        symbExHighlights.clear();

        try {
            for (int i = 0; i < lines.size(); i++) {
                Pair<Node, PositionInfo> l = lines.get(i);
                if (filename.equals(l.second.getFileName())) {
                    // use a different color for most recent
                    if (i == 0) {
                        symbExHighlights.add(addHighlight(
                                getSelectedFileName(),
                                l.second.getStartPosition().getLine() - 1,
                                MOST_RECENT_HIGHLIGHT_COLOR,
                                0));
                    } else {
                        symbExHighlights.add(addHighlight(
                                getSelectedFileName(),
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

    private void resetSelectionHighlight() throws BadLocationException, IOException {
        if (selectionHL != null) {
            removeHighlight(selectionHL);
        }

        selectionHL = addHighlight(
                getSelectedFileName(),
                1,
                CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR,
                Integer.MAX_VALUE - 1);
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
     * Clears cached files, lines, and existing tabs.
     */
    private void clearCaches() {
        files.clear();
        tabFiles.clear();
        highlights.clear();
        hashes.clear();
        sources.clear();
        lines = null;
        tabs.removeAll();
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

    /**
     * Initializes a new JTextPane with the source code from the file in the HashMap entry.
     * In addition, listeners are added and highlights are painted.
     * @param entry the HashMap entry containing the file
     */
    private void initTextPane(Entry<String, File> entry) {
        try {
            textPane = new JTextPane();
            textPanes.add(textPane);

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

            selectedFile = entry.getKey();
            String original = sources.get(selectedFile);
            String source = replaceTabs(original);
            LineInformation[] li = getLineInformation(selectedFile);

            JavaDocument doc = new JavaDocument();
            textPane.setDocument(doc);
            doc.insertString(0, source, new SimpleAttributeSet());

            calculateSymbExHighlights(entry.getKey());
            applyHighlights(entry.getKey());

            // add a listener to highlight the line currently pointed to
            resetSelectionHighlight();

            textPane.addMouseMotionListener(new MouseMotionListener() {
                @Override
                public void mouseMoved(MouseEvent e) {
                    paintSelectionHighlight(e.getPoint(), selectionHL);
                }

                @Override
                public void mouseDragged(MouseEvent e) { }
            });

            textPane.addMouseListener(new TextPaneMouseAdapter(
                    textPane, li, entry.getKey()));

            /* for each File, create a Tab in TabbedPane
             * (additional panel is needed to prevent line wrapping) */
            JPanel nowrap = new JPanel(new BorderLayout());
            nowrap.add(textPane);
            JScrollPane textScrollPane = new JScrollPane();
            textScrollPane.setViewportView(nowrap);
            textScrollPane.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            textScrollPane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED);

            // increase unit increment (for faster scrolling)
            textScrollPane.getVerticalScrollBar().setUnitIncrement(30);
            textScrollPane.getHorizontalScrollBar().setUnitIncrement(30);

            tabFiles.add(entry.getValue().getAbsolutePath());
            tabs.addTab(entry.getValue().getName(), textScrollPane);

            //add Line numbers to each Scrollview
            TextLineNumber tln = new TextLineNumber(textPane, 4);
            textScrollPane.setRowHeaderView(tln);

            // add the full path as tooltip for the tab
            int index = tabs.indexOfTab(entry.getValue().getName());
            tabs.setToolTipTextAt(index, entry.getValue().getAbsolutePath());
        } catch (BadLocationException | IOException e) {
            Debug.out(e);
        }
    }

    /**
     * Fills the HashMaps containing Files and translations from lines (in source code) to
     * corresponding nodes in proof tree.
     */
    private void fillMaps() {
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
    private boolean addFile(String filename) {
        File f = new File(filename);
        if (f.exists() && files.putIfAbsent(filename, f) == null) {
            try {
                String text = IOUtil.readFrom(f);
                if (text != null && !text.isEmpty()) {
                    hashes.put(filename, IOUtil.computeMD5(f));
                    sources.put(filename, text);
                }
            } catch (IOException e) {
                Debug.out("Unknown IOException!", e);
            }

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
        textPanes.clear();
        tabs.removeAll();

        if (currentNode == null) {
            tabs.setBorder(new TitledBorder(NO_SOURCE));
            sourceStatusBar.setText(NO_SOURCE);
            return;
        }

        // get PositionInfo of all symbEx nodes
        lines = constructLinesSet(currentNode);
        if (lines == null) {
            tabs.setBorder(new TitledBorder(NO_SOURCE));
            sourceStatusBar.setText(NO_SOURCE);
            return;
        }

        fillMaps();

        // create and initialize a new TextPane for every file
        for (Entry<String, File> entry : files.entrySet()) {
            initTextPane(entry);
        }
        if (tabs.getTabCount() > 0) {
            tabs.setBorder(new EmptyBorder(0, 0, 0, 0));

            // activate the tab with the most recent file
            PositionInfo p = lines.isEmpty() ? null : lines.getFirst().second;
            if (p != null) {
                File f = files.get(p.getFileName());
                if (f != null) {
                    String s = f.getName();
                    for (int i = 0; i < tabs.getTabCount(); i++) {
                        if (tabs.getTitleAt(i).equals(s)) {
                            tabs.setSelectedIndex(i);

                            // scroll to most recent highlight
                            int line = lines.getFirst().second.getEndPosition().getLine();
                            scrollNestedTextPaneToLine(tabs.getComponent(i), line, f);
                        }
                    }
                }
            }

            // set the path information in the status bar
            sourceStatusBar.setText(collectPathInformation(currentNode));
        } else {
            tabs.setBorder(new TitledBorder(NO_SOURCE));
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
            int line = posToLine(pos);

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
