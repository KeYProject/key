/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.sourceview;

import java.awt.*;
import java.awt.Dimension;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionAdapter;
import java.awt.event.MouseMotionListener;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.util.*;
import javax.swing.*;
import javax.swing.border.BevelBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.TitledBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.Document;
import javax.swing.text.Highlighter;
import javax.swing.text.Highlighter.HighlightPainter;
import javax.swing.text.SimpleAttributeSet;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.nodeviews.CurrentGoalView;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofJavaSourceCollection;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class is responsible for showing the source code and visualizing the symbolic execution path
 * of the currently selected node. This is done by adding tabs containing the source code and
 * highlighting the lines which were symbolically executed in the path from the root node down to
 * the current node. In addition, by clicking on such a highlighted line the user can jump to the
 * first node in the proof tree where a statement from this line is symbolically executed.
 *
 * Editing the source code in the tabs is currently not implemented (not supported by
 * {@link JavaDocument}).
 *
 * @author Wolfram Pfeifer, lanzinger
 */
public final class SourceView extends JComponent {
    private static final Logger LOGGER = LoggerFactory.getLogger(SourceView.class);

    private static final long serialVersionUID = -94424677425561025L;

    /**
     * the only instance of this singleton
     */
    private static SourceView instance;

    /**
     * ToolTip for the textPanes containing the source code.
     */
    private static final String TEXTPANE_HIGHLIGHTED_TOOLTIP =
        "Jump upwards to the most recent" + " occurrence of this line in symbolic execution.";

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
    private static final ColorSettings.ColorProperty NORMAL_HIGHLIGHT_COLOR =
        ColorSettings.define("[SourceView]normalHighlight",
            "Color for highlighting symbolically executed lines in source view",
            new Color(194, 245, 194));

    /**
     * The color of the most recent highlight in source code (green).
     */
    private static final ColorSettings.ColorProperty MOST_RECENT_HIGHLIGHT_COLOR =
        ColorSettings.define("[SourceView]mostRecentHighlight",
            "Color for highlighting most recently" + " symbolically executed line in source view",
            new Color(57, 210, 81));

    /**
     * The color of the most recent highlight in source code (green).
     */
    private static final ColorSettings.ColorProperty TAB_HIGHLIGHT_COLOR =
        ColorSettings.define("[SourceView]tabHighlight",
            "Color for highlighting source view tabs" + " whose files contain highlighted lines.",
            new Color(57, 210, 81));

    /**
     * The main window of KeY (needed to get the mediator).
     */
    private final MainWindow mainWindow;

    /**
     * Maps every file to a tab.
     */
    private final Map<URI, Tab> tabs = new HashMap<>();

    /**
     * Pane containing the tabs.
     */
    private final TabbedPane tabPane = new TabbedPane();

    /**
     * Currently selected file.
     */
    private URI selectedFile = null;

    /**
     * The status bar for displaying information about the current proof branch.
     */
    private final JLabel sourceStatusBar;

    /**
     * Lines to highlight (contains all highlights of the current proof) and corresponding Nodes.
     */
    private LinkedList<Pair<Node, PositionInfo>> lines;

    /** The symbolic execution highlights. */
    private final Set<Highlight> symbExHighlights = new HashSet<>();

    /**
     * Creates a new JComponent with the given MainWindow and adds change listeners.
     *
     * @param mainWindow the MainWindow of the GUI
     */
    private SourceView(MainWindow mainWindow) {
        super();
        this.mainWindow = mainWindow;

        sourceStatusBar = new JLabel();
        tabPane.setBorder(new TitledBorder(NO_SOURCE));

        tabPane.addChangeListener(e -> {
            if (tabPane.getSelectedTab() == null) {
                selectedFile = null;
            } else {
                selectedFile = tabPane.getSelectedTab().absoluteFileName;
            }

            // Mark tabs that contain highlights.
            for (Tab tab : tabs.values()) {
                tab.markTabComponent();
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
        Config.DEFAULT.addConfigChangeListener(e -> {
            for (Tab tab : tabs.values()) {
                tab.textPane.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
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

        KeYGuiExtensionFacade.installKeyboardShortcuts(null, this,
            KeYGuiExtension.KeyboardShortcuts.SOURCE_VIEW);

    }

    /**
     * Returns the singleton instance of the SourceView.
     *
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
     * <p>
     * Creates a new highlight.
     * </p>
     *
     * <p>
     * If the are multiple highlights for a given line, they are drawn on top of each other,
     * starting with the one with the lowest level.
     * </p>
     *
     * <p>
     * The highlights added by the {@code SourceView} itself have level {@code 0}, except for the
     * highlight that appears when the user moves the mouse over a line, which has level
     * {@code Integer.maxValue() - 1}.
     * </p>
     *
     * @param fileURI the URI of the file in which to create the highlight.
     * @param line the line to highlight.
     * @param color the color to use for the highlight.
     * @param level the level of the highlight.
     * @return the highlight.
     *
     * @throws BadLocationException if the line number is invalid.
     * @throws IOException if the file cannot be read.
     */
    public Highlight addHighlight(URI fileURI, int line, Color color, int level)
            throws BadLocationException, IOException {
        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        if (tab == null || line < 0 || line >= tab.lineInformation.length) {
            throw new BadLocationException("Not a valid line number for " + fileURI, line);
        }

        if (!tab.highlights.containsKey(line)) {
            tab.highlights.put(line, new TreeSet<>(Collections.reverseOrder()));
        }

        SortedSet<Highlight> highlights = tab.highlights.get(line);

        Highlight highlight = new Highlight(fileURI, line, color, level);
        highlights.add(highlight);

        tab.markTabComponent();

        tab.removeHighlights(line);
        tab.applyHighlights(line);

        return highlight;
    }

    /**
     * <p>
     * Creates a new set of highlights for a range of lines starting with {@code firstLine}.
     * </p>
     *
     * <p>
     * This method applies a heuristic to try and highlight the complete JML statement starting in
     * {@code firstLine}.
     * </p>
     *
     * @param fileURI the URI of the file in which to create the highlights.
     * @param firstLine the first line to highlight.
     * @param color the color to use for the highlights.
     * @param level the level of the highlights.
     * @return the highlights.
     *
     * @throws BadLocationException if the line number is invalid.
     * @throws IOException if the file cannot be read.
     */
    public Set<Highlight> addHighlightsForJMLStatement(URI fileURI, int firstLine, Color color,
            int level) throws BadLocationException, IOException {
        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        String[] lines = tab != null ? tab.source.split("\\R", -1) : new String[] {};

        // If we are in a JML comment, highlight everything until the next semicolon.
        // Otherwise, just highlight the first line.
        int lastLine = firstLine;
        if (0 < lines.length && lines[firstLine - 1].trim().startsWith("@")) {
            int parens = 0;

            outer_loop: for (int i = firstLine; i <= lines.length; ++i) {
                for (int j = 0; j < lines[i - 1].length(); ++j) {
                    if (lines[i - 1].charAt(j) == '(') {
                        ++parens;
                    } else if (lines[i - 1].charAt(j) == ')') {
                        --parens;
                    } else if (parens == 0 && lines[i - 1].charAt(j) == ';') {
                        lastLine = i;
                        break outer_loop;
                    }
                }
            }
        }

        Set<Highlight> result = new HashSet<>();

        for (int i = firstLine; i <= lastLine && tab != null; ++i) {
            result.add(addHighlight(fileURI, i, color, level));
        }

        return result;
    }

    /**
     * Moves an existing highlight to another line.
     *
     * @param highlight the highlight to change.
     * @param newLine the line to move the highlight to.
     *
     * @throws BadLocationException if the line number is invalid.
     */
    public void changeHighlight(Highlight highlight, int newLine) throws BadLocationException {
        URI fileURI = highlight.getFileURI();
        int oldLine = highlight.getLine();

        Tab tab = tabs.get(fileURI);

        if (tab == null || !tab.highlights.containsKey(oldLine)
                || !tab.highlights.get(oldLine).contains(highlight)) {
            throw new IllegalArgumentException("highlight");
        }

        tab.removeHighlights(oldLine);
        tab.highlights.get(oldLine).remove(highlight);
        tab.applyHighlights(oldLine);

        if (tab.highlights.get(oldLine).isEmpty()) {
            tab.highlights.remove(oldLine);
        }

        highlight.line = newLine;
        highlight.setTag(null);

        if (!tab.highlights.containsKey(newLine)) {
            tab.highlights.put(newLine, new TreeSet<>());
        }

        tab.highlights.get(newLine).add(highlight);
        tab.removeHighlights(newLine);
        tab.applyHighlights(newLine);
    }

    /**
     * Removes a highlight.
     *
     * @param highlight the highlight to remove.
     * @return {@code true} iff this {@code SourceView} previously contained the specified
     *         highlight.
     */
    public boolean removeHighlight(Highlight highlight) {
        Tab tab = tabs.get(highlight.getFileURI());

        if (tab == null) {
            return false;
        }

        tab.removeHighlights(highlight.getLine());

        boolean result = tab.highlights.containsKey(highlight.getLine())
                && tab.highlights.get(highlight.getLine()).remove(highlight);
        highlight.setTag(null);

        if (result && tab.highlights.get(highlight.getLine()).isEmpty()) {
            tab.highlights.remove(highlight.getLine());
        } else {
            try {
                tab.applyHighlights(highlight.getLine());
            } catch (BadLocationException e) {
                // The locations of the highlights have already been checked
                // in addHighlight & changeHighlight, so no error can occur here.
                throw new AssertionError();
            }
        }

        tab.markTabComponent();

        return result;
    }

    /**
     * Adds an additional tab for the specified file.
     *
     * @param fileURI the URI of the file to open.
     *
     * @throws IOException if the file cannot be opened.
     */
    public void openFile(URI fileURI) throws IOException {
        openFiles(Collections.singleton(fileURI));
    }

    /**
     * Adds additional tabs for the specified files.
     *
     * @param fileURIs the URIs of the files to open.
     *
     * @throws IOException if one of the files cannot be opened.
     */
    public void openFiles(Iterable<URI> fileURIs) throws IOException {
        boolean updateNecessary = false;

        for (URI fileURI : fileURIs) {
            if (addFile(fileURI)) {
                updateNecessary = true;
                mainWindow.getMediator().getSelectedProof().lookup(ProofJavaSourceCollection.class)
                        .addRelevantFile(fileURI);
            }
        }

        if (updateNecessary) {
            updateGUI();
        }
    }

    /**
     * Calculates the range of actual text (not whitespace) in the line containing the given
     * position.
     *
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
            LOGGER.debug("Caught exception!", e);
        }

        // find line end
        int end = text.indexOf('\n', pos);
        end = end == -1 ? text.length() : end; // last line?

        // find line start
        int start = text.lastIndexOf('\n', pos - 1); // TODO: different line endings?
        start = start == -1 ? 0 : start; // first line?

        // ignore whitespace at the beginning of the line
        while (start < text.length() && start < end && Character.isWhitespace(text.charAt(start))) {
            start++;
        }

        return new Range(start, end);
    }

    /**
     * Replaces each tab in the given String by TAB_SIZE spaces.
     *
     * @param s the String to replace
     * @return the resulting String (without tabs)
     */
    private static String replaceTabs(String s) {
        // fill a new array with the specified amount of spaces
        char[] rep = new char[TAB_SIZE];
        Arrays.fill(rep, ' ');
        return s.replace("\t", new String(rep));
    }

    private boolean isSelected(Tab tab) {
        return Objects.equals(selectedFile, tab.absoluteFileName);
    }

    /**
     * Checks if the given point is highlighted (by a symbolic execution highlight) inside the
     * active tab. Due to technical restrictions of the method viewToModel(Point), the result is a
     * little bit imprecise: The last char in a line is not detected as highlighted, this method
     * wrongly returns false.
     *
     * @param point the point to check, usually the position of the mouse cursor
     * @return true iff the point is on a highlight
     */
    private boolean isHighlighted(Point point) {
        Tab tab = tabs.get(selectedFile);
        int pos = tab.textPane.viewToModel(point);
        int line = tab.posToLine(pos);

        for (Highlight h : symbExHighlights) {
            if (line == h.line) {
                // found matching highlight h: Is the mouse cursor inside the highlight?
                Range range =
                    calculateLineRange(tab.textPane, tab.lineInformation[line - 1].getOffset());
                // we need < here, since viewToModel can not return a position after the last
                // char in a line
                if (range.start() <= pos && pos < range.end()) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Adds all files relevant to the currently selected node, closing all others
     *
     * @see NodeInfo#getRelevantFiles()
     */
    private void addFiles() {
        ImmutableSet<URI> fileURIs = mainWindow.getMediator().getSelectedProof()
                .lookup(ProofJavaSourceCollection.class).getRelevantFiles();

        Iterator<URI> it = tabs.keySet().iterator();

        while (it.hasNext()) {
            URI fileURI = it.next();

            if (!fileURIs.contains(fileURI)) {
                Tab tab = tabs.get(fileURI);
                it.remove();
                tabPane.remove(tab);
            }
        }

        for (URI fileURI : fileURIs) {
            try {
                addFile(fileURI);
            } catch (IOException e) {
                LOGGER.debug("Exception while adding file: ", e);
            }
        }
    }

    /**
     * Adds a file (identified by its URI) to this source view.
     *
     * @param fileURI the URI of the file to add.
     * @return {@code true} if this source view did not already contain the file.
     * @throws IOException if the file cannot be opened.
     */
    private boolean addFile(URI fileURI) throws IOException {
        // quick fix: fileName could be null (see bug #1520)
        if (fileURI == null || tabs.containsKey(fileURI)) {
            return false;
        } else {
            // try to load the file via the FileRepo
            Proof proof = mainWindow.getMediator().getSelectedProof();
            FileRepo repo = proof.getInitConfig().getFileRepo();

            try (InputStream is = repo.getInputStream(fileURI.toURL())) {
                if (is != null) {
                    Tab tab = new Tab(fileURI, is);
                    tabs.put(fileURI, tab);
                    // filename as tab title, complete file URI as tooltip
                    tabPane.addTab(tab.simpleFileName, tab);
                    int index = tabPane.indexOfComponent(tab);
                    tabPane.setToolTipTextAt(index, tab.absoluteFileName.toString());
                    tab.paintSymbExHighlights();
                    return true;
                }
            }
        }
        throw new IOException("Could not open file: " + fileURI);
    }

    private void clear() {
        lines = null;
        tabs.forEach((a, b) -> b.dispose());
        tabs.clear();
        tabPane.removeAll();
    }

    /**
     * Performs an update of the GUI:
     * <ul>
     * <li>updates the TabbedPane with the source files used</li>
     * <li>highlights the symbolically executed lines</li>
     * <li>updates the source status bar of the main window with information about the current
     * branch</li>
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

        tabs.values().forEach(Tab::paintSymbExHighlights);

        if (tabPane.getTabCount() > 0) {
            tabPane.setBorder(new EmptyBorder(0, 0, 0, 0));

            // activate the tab with the most recent file
            PositionInfo p = lines.isEmpty() ? null : lines.getFirst().second;
            if (p != null) {
                Tab t = tabs.get(p.getURI().orElse(null));
                if (t != null) {
                    String s = t.simpleFileName;
                    for (int i = 0; i < tabPane.getTabCount(); i++) {
                        if (tabPane.getTitleAt(i).equals(s)) {
                            tabPane.setSelectedIndex(i);

                            // scroll to most recent highlight
                            int line = lines.getFirst().second.getEndPosition().line();
                            t.scrollToLine(line);
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

    private void addPosToList(PositionInfo pos, LinkedList<Pair<Node, PositionInfo>> list,
            Node node) {
        if (pos != null && !pos.equals(PositionInfo.UNDEFINED) && pos.startEndValid()
                && pos.getURI().isPresent()) {
            list.addLast(new Pair<>(node, pos));
            node.proof().lookup(ProofJavaSourceCollection.class)
                    .addRelevantFile(pos.getURI().get());
        }
    }

    /**
     * Collects the set of lines to highlight starting from the given node in the proof tree.
     *
     * @param node the given node
     * @return a linked list of pairs of PositionInfo objects containing the start and end positions
     *         for the highlighting and Nodes.
     */
    private LinkedList<Pair<Node, PositionInfo>> constructLinesSet(Node node) {
        LinkedList<Pair<Node, PositionInfo>> list = new LinkedList<>();

        if (node == null) {
            return null;
        }

        Node cur = node;

        do {
            SourceElement activeStatement = cur.getNodeInfo().getActiveStatement();
            if (activeStatement != null) {
                addPosToList(joinPositionsRec(activeStatement), list, cur);
            }
            cur = cur.parent();

        } while (cur != null);

        if (list.isEmpty()) {
            // If the list is empty, search the sequent for method body statements
            // and add the files containing the called methods.
            // This is a hack to make sure that the file containing the method which the current
            // proof obligation belongs to is always loaded.

            node.sequent().forEach(
                formula -> formula.formula().execPostOrder(new de.uka.ilkd.key.logic.Visitor() {

                    @Override
                    public boolean visitSubtree(Term visited) {
                        return visited.containsJavaBlockRecursive();
                    }

                    @Override
                    public void visit(Term visited) {}

                    @Override
                    public void subtreeLeft(Term subtreeRoot) {}

                    @Override
                    public void subtreeEntered(Term subtreeRoot) {
                        if (subtreeRoot.javaBlock() != null) {
                            JavaASTVisitor visitor =
                                new JavaASTVisitor(subtreeRoot.javaBlock().program(),
                                    mainWindow.getMediator().getServices()) {

                                    @Override
                                    protected void doDefaultAction(SourceElement el) {
                                        if (el instanceof MethodBodyStatement) {
                                            MethodBodyStatement mb = (MethodBodyStatement) el;
                                            Statement body = mb.getBody(services);
                                            PositionInfo posInf = null;
                                            // try to find position information of the source
                                            // element
                                            if (body != null) {
                                                posInf = body.getPositionInfo();
                                            } else {
                                                // the method is declared without a body
                                                // -> we try to show the file either way
                                                IProgramMethod pm = mb.getProgramMethod(services);
                                                if (pm != null) {
                                                    posInf = pm.getPositionInfo();
                                                }
                                            }
                                            if (posInf != null && posInf.getURI().isPresent()) {
                                                // sometimes the useful file info is only stored in
                                                // parentClassURI for some reason ...
                                                if (posInf.getURI().isPresent()) {
                                                    node.proof()
                                                            .lookup(ProofJavaSourceCollection.class)
                                                            .addRelevantFile(posInf.getURI().get());
                                                } else if (posInf.getParentClassURI() != null) {
                                                    node.proof()
                                                            .lookup(ProofJavaSourceCollection.class)
                                                            .addRelevantFile(
                                                                posInf.getParentClassURI());
                                                }
                                            }
                                        }
                                    }
                                };
                            visitor.start();
                        }
                    }
                }));
        }

        return list;
    }

    /**
     * Joins all PositionInfo objects of the given SourceElement and its children.
     *
     * @param se the given SourceElement
     * @return a new PositionInfo starting at the minimum of all the contained positions and ending
     *         at the maximum position
     */
    private static PositionInfo joinPositionsRec(SourceElement se) {
        if (se instanceof NonTerminalProgramElement) {
            // TODO: additional elements, e.g. code inside if
            if (se instanceof If || se instanceof Then || se instanceof Else) {
                return PositionInfo.UNDEFINED;
            }

            NonTerminalProgramElement ntpe = (NonTerminalProgramElement) se;
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
     * <li>Invariant Initially Valid</li>
     * <li>Body Preserves Invariant</li>
     * <li>Use Case</li>
     * <li>...</li>
     * </ul>
     *
     * @param node the current node
     * @return a String containing the path information to display
     */
    private static String collectPathInformation(Node node) {
        while (node != null) {
            if (node.getNodeInfo() != null && node.getNodeInfo().getBranchLabel() != null) {
                String label = node.getNodeInfo().getBranchLabel();
                /*
                 * Are there other interesting labels? Please feel free to add them here.
                 */
                if (label.equals("Invariant Initially Valid")
                        || label.equals("Invariant Preserved and Used") // for loop scope invariant
                        || label.equals("Body Preserves Invariant") || label.equals("Use Case")
                        || label.equals("Show Axiom Satisfiability") || label.startsWith("Pre (")
                        || label.startsWith("Exceptional Post (") // exceptional postcondition
                        || label.startsWith("Post (") // postcondition of a method
                        || label.contains("Normal Execution") || label.contains("Null Reference")
                        || label.contains("Index Out of Bounds") || label.contains("Validity")
                        || label.contains("Precondition") || label.contains("Usage")) {
                    return label;
                }
            }
            node = node.parent();
        }
        // if no label was found we have to prove the postcondition
        return "Show Postcondition/Assignable";
    }

    /**
     * The type of the tabbed pane contained in this {@code SourceView}.
     *
     * @author lanzinger
     * @see #tabPane
     */
    private final static class TabbedPane extends JTabbedPane {
        private static final long serialVersionUID = -5438740208669700183L;

        Tab getSelectedTab() {
            return (Tab) getSelectedComponent();
        }
    }

    /**
     * Wrapper for all tab-specific data, i.e., all data pertaining to the file shown in the tab.
     *
     * @author Wolfram Pfeifer
     * @author lanzinger
     */
    private final class Tab extends JScrollPane {
        private static final long serialVersionUID = -8964428275919622930L;

        /**
         * The file this tab belongs to.
         */
        private final URI absoluteFileName;

        /**
         * The file this tab belongs to.
         */
        private final String simpleFileName;

        /**
         * The text pane containing the file's content.
         */
        private final JTextPane textPane = new JTextPane() {
            @Override
            public String getToolTipText(MouseEvent mouseEvent) {
                if (!ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                        .isShowSourceViewTooltips()) {
                    return null;
                }

                if (isHighlighted(mouseEvent.getPoint())) {
                    return TEXTPANE_HIGHLIGHTED_TOOLTIP;
                }
                return null;
            }
        };

        /**
         * The line information for the file this tab belongs to.
         */
        private LineInformation[] lineInformation;

        /**
         * The file's content with tabs replaced by spaces.
         */
        private String source;

        /**
         * The highlight for the user's selection.
         */
        private Highlight selectionHL;

        /**
         * Maps line numbers to highlights.
         */
        private final Map<Integer, SortedSet<Highlight>> highlights = new HashMap<>();

        /**
         * The JavaDocument shown in this tab.
         */
        private JavaDocument doc = null;

        private Tab(URI fileURI, InputStream stream) {
            this.absoluteFileName = fileURI;
            this.simpleFileName = extractFileName(fileURI);

            try {
                String text = IOUtil.readFrom(stream);
                if (text != null && !text.isEmpty()) {
                    source = replaceTabs(text);
                } else {
                    source = "[SOURCE COULD NOT BE LOADED]";
                }
            } catch (IOException e) {
                source = "[SOURCE COULD NOT BE LOADED]";
                LOGGER.debug("Unknown IOException!", e);
            }

            initLineInfo();

            initTextPane();

            JPanel nowrap = new JPanel(new BorderLayout());
            nowrap.add(textPane);
            setViewportView(nowrap);
            setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED);

            // increase unit increment (for faster scrolling)
            getVerticalScrollBar().setUnitIncrement(30);
            getHorizontalScrollBar().setUnitIncrement(30);

            // add Line numbers to each Scrollview
            TextLineNumber tln = new TextLineNumber(textPane, 1);
            tln.setUpdateFont(true);
            setRowHeaderView(tln);
        }

        private String extractFileName(URI uri) {
            String s = uri.toString();
            int index = s.lastIndexOf('/');
            if (index < 0) {
                return s; // fallback: return whole URI
            } else {
                return s.substring(index + 1);
            }
        }

        private void initLineInfo() {
            try {
                InputStream inStream =
                    new ByteArrayInputStream(source.getBytes(StandardCharsets.UTF_8));
                lineInformation = IOUtil.computeLineInformation(inStream);
            } catch (IOException e) {
                LOGGER.debug("Error while computing line information from {}", absoluteFileName, e);
            }
        }

        private void initTextPane() {
            // We use the same font as in SequentView for consistency.
            textPane.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
            textPane.setToolTipText("");
            textPane.setEditable(false);
            textPane.addMouseMotionListener(new MouseMotionAdapter() {
                @Override
                public void mouseMoved(MouseEvent mouseEvent) {
                    if (isHighlighted(mouseEvent.getPoint())) {
                        textPane.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
                    } else {
                        textPane.setCursor(Cursor.getDefaultCursor());
                    }
                }
            });

            // insert source code into text pane
            try {
                doc = new JavaDocument();
                textPane.setDocument(doc);
                doc.insertString(0, source, new SimpleAttributeSet());
            } catch (BadLocationException e) {
                throw new AssertionError();
            }

            // add a listener to highlight the line currently pointed to
            textPane.addMouseMotionListener(new MouseMotionListener() {
                @Override
                public void mouseMoved(MouseEvent e) {
                    synchronized (SourceView.this) {
                        if (selectionHL != null) {
                            paintSelectionHighlight(e.getPoint(), selectionHL);
                        }
                    }
                }

                @Override
                public void mouseDragged(MouseEvent e) {}
            });

            textPane.addMouseListener(new MouseAdapter() {

                @Override
                public void mouseExited(MouseEvent e) {
                    synchronized (SourceView.this) {
                        if (selectionHL != null) {
                            removeHighlight(selectionHL);
                            selectionHL = null;
                        }
                    }
                }

                @Override
                public void mouseEntered(MouseEvent e) {
                    synchronized (SourceView.this) {
                        if (selectionHL == null) {
                            initSelectionHL();
                        }
                    }
                }
            });

            textPane.addMouseListener(
                new TextPaneMouseAdapter(textPane, lineInformation, absoluteFileName));
        }

        private void markTabComponent() {
            if (highlights.isEmpty()) {
                tabPane.setForegroundAt(tabPane.indexOfComponent(this),
                    UIManager.getColor("TabbedPane.foreground"));
                tabPane.setBackgroundAt(tabPane.indexOfComponent(this),
                    UIManager.getColor("TabbedPane.background"));
            } else {
                if (isSelected(this)) {
                    tabPane.setForegroundAt(tabPane.indexOfComponent(this),
                        TAB_HIGHLIGHT_COLOR.get());
                    tabPane.setBackgroundAt(tabPane.indexOfComponent(this),
                        UIManager.getColor("TabbedPane.background"));
                } else {
                    tabPane.setForegroundAt(tabPane.indexOfComponent(this),
                        UIManager.getColor("TabbedPane.foreground"));
                    tabPane.setBackgroundAt(tabPane.indexOfComponent(this),
                        TAB_HIGHLIGHT_COLOR.get());
                }
            }
        }

        private void initSelectionHL() {
            try {
                selectionHL = addHighlight(absoluteFileName, 1,
                    CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR.get(), Integer.MAX_VALUE - 1);
            } catch (BadLocationException | IOException e) {
                LOGGER.debug("Caught exception!", e);
            }
        }

        private void removeHighlights(int line) {
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

        private void applyHighlights(int line) throws BadLocationException {
            SortedSet<Highlight> set = highlights.get(line);

            if (set != null && !set.isEmpty()) {
                for (Highlight highlight : set) {
                    Range range = calculateLineRange(textPane,
                        lineInformation[highlight.getLine() - 1].getOffset());

                    Color c = highlight.getColor();
                    int alpha = set.size() == 1 ? c.getAlpha() : 256 / set.size();
                    Color color = new Color(c.getRed(), c.getGreen(), c.getBlue(), alpha);

                    highlight.setTag(textPane.getHighlighter().addHighlight(range.start(),
                        range.end(), new DefaultHighlightPainter(color)));
                }
            }

            textPane.revalidate();
            textPane.repaint();
        }

        /**
         * Paints the highlights for symbolically executed lines. The most recently executed line is
         * highlighted with a different color.
         */
        private void paintSymbExHighlights() {
            for (Highlight hl : symbExHighlights) {
                removeHighlight(hl);
            }

            symbExHighlights.clear();

            if (lines == null) {
                return;
            }

            try {
                int mostRecentLine = -1;

                for (int i = 0; i < lines.size(); i++) {
                    Pair<Node, PositionInfo> l = lines.get(i);

                    if (absoluteFileName.equals(l.second.getURI().orElse(null))) {
                        int line = l.second.getStartPosition().line();

                        // use a different color for most recent
                        if (i == 0) {
                            mostRecentLine = line;
                            symbExHighlights.add(addHighlight(absoluteFileName, line,
                                MOST_RECENT_HIGHLIGHT_COLOR.get(), 0));
                        } else if (line != mostRecentLine) {
                            symbExHighlights.add(addHighlight(absoluteFileName, line,
                                NORMAL_HIGHLIGHT_COLOR.get(), 0));
                        }
                    }
                }
            } catch (BadLocationException | IOException e) {
                LOGGER.debug("Caught exception!", e);
            }
        }

        /**
         * Paints the highlight for the line where the mouse pointer currently points to.
         *
         * @param p the current position of the mouse pointer
         * @param highlight the highlight to change
         */
        private void paintSelectionHighlight(Point p, Highlight highlight) {
            try {
                int line = posToLine(textPane.viewToModel(p));
                changeHighlight(highlight, line);
            } catch (BadLocationException e) {
                LOGGER.debug("Caught exception!", e);
            }
        }

        private int posToLine(int pos) {
            return textPane.getDocument().getDefaultRootElement().getElementIndex(pos) + 1;
        }

        private void scrollToLine(int line) {
            int offs = lineInformation[line].getOffset();
            textPane.setCaretPosition(offs);
        }

        private void dispose() {
            if (doc != null) {
                doc.dispose();
            }
        }
    }

    /**
     * <p>
     * An object of this class represents a highlight of a specific line in the {@code SourceView}.
     * </p>
     *
     * @author lanzinger
     *
     * @see SourceView#addHighlight(URI, int, Color, int)
     * @see SourceView#changeHighlight(Highlight, int)
     * @see SourceView#removeHighlight(Highlight)
     */
    public static final class Highlight implements Comparable<Highlight> {

        /** @see #getTag() */
        private static final Map<Highlight, Object> TAGS = new HashMap<>();

        /** @see #getLevel() */
        private final int level;

        /** @see #getColor() */
        private final Color color;

        /** @see #getFileURI() */
        private final URI fileURI;

        /** @see #getLine() */
        private int line;

        /**
         * Creates a new highlight.
         *
         * @param fileURI URI of the file in which this highlight is used.
         * @param line the line being highlighted.
         * @param color this highlight's color.
         * @param level this highlight's level.
         */
        private Highlight(URI fileURI, int line, Color color, int level) {
            this.level = level;
            this.color = color;
            this.fileURI = fileURI;
            this.line = line;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((color == null) ? 0 : color.hashCode());
            result = prime * result + ((fileURI == null) ? 0 : fileURI.hashCode());
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
            if (fileURI == null) {
                if (other.fileURI != null) {
                    return false;
                }
            } else if (!fileURI.equals(other.fileURI)) {
                return false;
            }
            if (level != other.level) {
                return false;
            }
            return line == other.line;
        }

        @Override
        public int compareTo(Highlight other) {
            int result = fileURI.compareTo(other.fileURI);

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
                TAGS.remove(this);
            } else {
                TAGS.put(this, tag);
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
            return TAGS.get(this);
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
        public URI getFileURI() {
            return fileURI;
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
    private final class TextPaneMouseAdapter extends MouseAdapter {
        /**
         * The precalculated start indices of the lines. Used to compute the clicked line number.
         */
        final LineInformation[] li;

        /**
         * The JTextPane containing the source code.
         */
        final JTextPane textPane;

        /**
         * The URI of the file whose content is displayed in the JTextPane.
         */
        final URI fileURI;

        private TextPaneMouseAdapter(JTextPane textPane, LineInformation[] li, URI fileURI) {
            this.textPane = textPane;
            this.li = li;
            this.fileURI = fileURI;
        }

        @Override
        public void mouseClicked(MouseEvent e) {
            int pos = textPane.viewToModel(e.getPoint());
            if (isHighlighted(e.getPoint())) {
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
                    if (p.second.getStartPosition().line() == line + 1
                            && p.second.getURI().equals(fileURI)) {
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
