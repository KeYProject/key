package de.uka.ilkd.key.gui.sourceview;

import static de.uka.ilkd.key.gui.nodeviews.CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR;

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
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

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
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.Document;
import javax.swing.text.Highlighter.Highlight;
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

    /* TODO: make proof independent, move sources and hashes to proof.services.JavaModel or similar
     * There is still a consistency problem here if the proof is change: In that case the code is
     * silently reloaded from the (possibly changed) file. This will be solved in future work.
     * Corresponding feature request:
     */
    /**
     * HashMap mapping filenames to files (of the current proof!).
     */
    private HashMap<String, File> files = new HashMap<String, File>();

    /**
     * HashMap mapping filenames to hashes of the content (files of the current proof!).
     */
    private HashMap<String, String> hashes = new HashMap<String, String>();

    /**
     * HashMap mapping filenames to content strings (files of the current proof!).
     */
    private HashMap<String, String> sources = new HashMap<String, String>();

    /**
     * Lines to highlight (contains all highlights of the current proof) and corresponding Nodes.
     */
    private LinkedList<Pair<Node, PositionInfo>> lines;

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
         * The Painter used for painting the highlights (except for the most recent one).
         */
        final HighlightPainter painter;

        /**
         * The JTextPane containing the source code.
         */
        final JTextPane textPane;

        /**
         * The filename of the file whose content is displayed in the JTextPane.
         */
        final String filename;

        public TextPaneMouseAdapter(JTextPane textPane, LineInformation[] li,
                HighlightPainter painter, String filename) {
            this.textPane = textPane;
            this.li = li;
            this.painter = painter;
            this.filename = filename;
        }

        /**
         * Checks if the given position is within a highlight.
         * @param pos the position to check
         * @return true if highlighted and false if not
         */
        private boolean isHighlighted(int pos) {
            Highlight[] hs = textPane.getHighlighter().getHighlights();
            for (Highlight h : hs) {
                // search for highlight by the same painter
                if (h.getPainter() == painter) {
                    // check if the position is within the highlighted range
                    if (h.getStartOffset() <= pos && h.getEndOffset() >= pos) {
                        return true;
                    }
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

    /**
     * Paints the highlights for symbolically executed lines. The most recently executed line is
     * highlighted with a different color.
     * @param textPane the JTextPane containing the source code
     * @param li precalculated start indices of the lines
     * @param filename the filename corresponding to the given JTextPane
     * @param hp the painter to use for highlighting
     */
    private void paintSymbExHighlights(JTextPane textPane, LineInformation[] li, String filename,
            HighlightPainter hp) {
        try {
            for (int i = 0; i < lines.size(); i++) {
                Pair<Node, PositionInfo> l = lines.get(i);
                if (filename.equals(l.second.getFileName())) {
                    Range r = calculateLineRange(textPane,
                            li[l.second.getStartPosition().getLine() - 1].getOffset());
                    // use a different color for most recent
                    if (i == 0) {
                        textPane.getHighlighter().addHighlight(r.start(), r.end(),
                                new DefaultHighlightPainter(MOST_RECENT_HIGHLIGHT_COLOR));
                    } else {
                        textPane.getHighlighter().addHighlight(r.start(), r.end(), hp);
                    }
                }
            }
        } catch (BadLocationException e) {
            Debug.out(e);
        }
    }

    /**
     * Paints the highlight for the line where the mouse pointer currently points to.
     * @param textPane the textPane to highlight lines
     * @param p the current position of the mouse pointer
     * @param tag the highlight to change
     */
    private static void paintSelectionHighlight(JTextPane textPane, Point p, Object tag) {
        Range r = calculateLineRange(textPane, p);
        try {
            textPane.getHighlighter().changeHighlight(tag, r.start(), r.end());
        } catch (BadLocationException e) {
            Debug.out(e);
        }
    }

    /**
     * Calculates the range of actual text (not whitespace) in the line under the given point.
     * @param textPane the JTextPane with the text
     * @param p the point to check
     * @return the range of text (may be empty if there is just whitespace in the line)
     */
    private static Range calculateLineRange(JTextPane textPane, Point p) {
        return calculateLineRange(textPane, textPane.viewToModel(p));
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
            JTextPane textPane = new JTextPane();
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

            String original = sources.get(entry.getKey());
            String source = replaceTabs(original);  // replace all tabs by spaces

            // use input stream here to compute line information of the string with replaced tabs
            InputStream inStream = new ByteArrayInputStream(source.getBytes());
            LineInformation[] li = IOUtil.computeLineInformation(inStream);

            JavaDocument doc = new JavaDocument();
            textPane.setDocument(doc);
            doc.insertString(0, source, new SimpleAttributeSet());

            // add a listener to highlight the line currently pointed to
            Object selectionHL = textPane.getHighlighter().addHighlight(0, 0,
                    new DefaultHighlightPainter(DEFAULT_HIGHLIGHT_COLOR));
            textPane.addMouseMotionListener(new MouseMotionListener() {
                @Override
                public void mouseMoved(MouseEvent e) {
                    paintSelectionHighlight(textPane, e.getPoint(), selectionHL);
                }

                @Override
                public void mouseDragged(MouseEvent e) {
                }
            });

            // paint the highlights (symbolically executed lines) for this file
            HighlightPainter hp = new DefaultHighlightPainter(NORMAL_HIGHLIGHT_COLOR);
            paintSymbExHighlights(textPane, li, entry.getKey(), hp);

            textPane.addMouseListener(new TextPaneMouseAdapter(textPane, li, hp, entry.getKey()));

            /* for each File, create a Tab in TabbedPane
             * (additional panel is needed to prevent line wrapping) */
            JPanel nowrap = new JPanel(new BorderLayout());
            nowrap.add(textPane);
            JScrollPane textScrollPane = new JScrollPane();
            textScrollPane.setViewportView(nowrap);
            textScrollPane.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            textScrollPane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED);
            tabs.addTab(entry.getValue().getName(), textScrollPane);

            // add the full path as tooltip for the tab
            int index = tabs.indexOfTab(entry.getValue().getName());
            tabs.setToolTipTextAt(index, entry.getValue().getAbsolutePath());
        } catch (IOException e) {
            Debug.out("An error occurred while reading " + entry.getValue().getAbsolutePath(), e);
        } catch (BadLocationException e) {
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
            File f = new File(l.getFileName());
            if (f.exists() && files.putIfAbsent(l.getFileName(), f) == null) {
                try {
                    String text = IOUtil.readFrom(f);
                    if (text != null && !text.isEmpty()) {
                        hashes.put(l.getFileName(), IOUtil.computeMD5(f));
                        sources.put(l.getFileName(), text);
                    }
                } catch (IOException e) {
                    Debug.out("Unknown IOException!", e);
                }
            }
        }
    }

    /**
     * Returns the singleton instance of the SourceView.
     * @param mainWindow KeY's main window
     * @return the component responsible for showing source code and symbolic execution information
     */
    public static JComponent getSourceView(MainWindow mainWindow) {
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
                    PositionInfo pos = joinPositionsRec((SourceElement)activeStatement);

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
}
