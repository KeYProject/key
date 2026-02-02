/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.sourceview;

import java.awt.*;
import java.awt.Dimension;
import java.awt.event.*;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.List;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import javax.swing.*;
import javax.swing.border.BevelBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.LineBorder;
import javax.swing.border.TitledBorder;
import javax.swing.text.*;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;

import bibliothek.util.container.Tuple;
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
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofJavaSourceCollection;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.jspecify.annotations.Nullable;
import org.key_project.logic.Visitor;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * <p>
 * This class is responsible for showing the source code and visualizing the symbolic execution path
 * of the currently selected node. This is done by adding tabs containing the source code and
 * highlighting the lines which were symbolically executed in the path from the root node down to
 * the current node. In addition, by clicking on such a highlighted line the user can jump to the
 * first node in the proof tree where a statement from this line is symbolically executed.
 * </p>
 * <p>
 * Editing the source code in the tabs is currently not implemented (not supported by
 * {@link JavaDocument}).
 * </p>
 *
 * @author Wolfram Pfeifer, lanzinger
 */
public final class SourceView extends JComponent {
    private static final Logger LOGGER = LoggerFactory.getLogger(SourceView.class);

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
     * Panel to display errors/warnings/etc
     */
    private final JPanel errorPane;
    private final JLabel errorText;
    private final JPanel errorCenter;
    private final JLabel infoText;
    private final JPanel infoCenter;
    private final JPanel infoWrap;

    /**
     * Lines to highlight (contains all highlights of the current proof) and corresponding Nodes.
     */
    private LinkedList<Pair<Node, PositionInfo>> lines;

    /** The symbolic execution highlights. */
    private final Set<SourceViewHighlight> symbExHighlights = new HashSet<>();

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

        {
            errorPane = new JPanel(new GridBagLayout());

            errorPane.setBackground(Color.WHITE);

            errorCenter = new JPanel(new BorderLayout());
            errorCenter.setBackground(new Color(255, 128, 128));
            errorCenter.setBorder(new LineBorder(Color.BLACK, 1));

            errorText = new JLabel("");
            errorText.setHorizontalAlignment(JLabel.CENTER);
            errorText.setVerticalAlignment(JLabel.CENTER);
            errorText.setHorizontalTextPosition(JLabel.CENTER);
            errorText.setVerticalTextPosition(JLabel.CENTER);
            errorText.setBorder(new EmptyBorder(8, 8, 8, 8));

            errorCenter.add(errorText);
            errorPane.add(errorCenter, new GridBagConstraints());
        }

        setLayout(new BorderLayout());
        add(tabPane, BorderLayout.CENTER);
        add(sourceStatusBar, BorderLayout.SOUTH);

        {
            infoWrap = new JPanel(new BorderLayout());
            infoWrap.setBorder(new EmptyBorder(4, 4, 4, 4));

            infoCenter = new JPanel(new BorderLayout());
            infoCenter.setBackground(new Color(64, 64, 255));
            infoCenter.setBorder(new LineBorder(Color.BLACK, 1));

            infoText = new JLabel("");
            infoText.setHorizontalAlignment(JLabel.LEFT);
            infoText.setVerticalAlignment(JLabel.CENTER);
            infoText.setHorizontalTextPosition(JLabel.LEFT);
            infoText.setVerticalTextPosition(JLabel.CENTER);
            infoText.setBorder(new EmptyBorder(8, 8, 8, 8));

            infoCenter.add(infoText);

            infoWrap.add(infoCenter);
            infoWrap.setVisible(false);

            add(infoWrap, BorderLayout.NORTH);
        }

        // react to font changes
        Config.DEFAULT.addConfigChangeListener(e -> {
            for (Tab tab : tabs.values()) {
                tab.textPane.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
            }
        });

        if (mainWindow.getMediator().getSelectedProof() != null) {
            ensureProofJavaSourceCollectionExists(mainWindow.getMediator().getSelectedProof());
        }

        // add a listener for changes in the proof tree
        mainWindow.getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
                if (!mainWindow.getMediator().isInAutoMode()) {
                    updateGUI();
                }
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                clear();
                ensureProofJavaSourceCollectionExists(e.getSource().getSelectedProof());
                updateGUI();
            }
        });

        KeYGuiExtensionFacade.installKeyboardShortcuts(null, this,
            KeYGuiExtension.KeyboardShortcuts.SOURCE_VIEW);

    }

    private void ensureProofJavaSourceCollectionExists(Proof proof) {
        if (proof != null && proof.lookup(ProofJavaSourceCollection.class) == null) {
            final var sources = new ProofJavaSourceCollection();
            proof.register(sources, ProofJavaSourceCollection.class);
            proof.root().sequent().forEach(formula -> {
                OriginTermLabel originLabel =
                    (OriginTermLabel) ((JTerm) formula.formula()).getLabel(OriginTermLabel.NAME);
                if (originLabel != null) {
                    if (originLabel.getOrigin() instanceof OriginTermLabel.FileOrigin) {
                        ((OriginTermLabel.FileOrigin) originLabel.getOrigin())
                                .getFileName()
                                .ifPresent(sources::addRelevantFile);
                    }

                    originLabel.getSubtermOrigins().stream()
                            .filter(o -> o instanceof OriginTermLabel.FileOrigin)
                            .map(o -> (OriginTermLabel.FileOrigin) o)
                            .forEach(o -> o.getFileName().ifPresent(sources::addRelevantFile));
                }
            });
        }


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
     * @param sourceLine the line to highlight.
     * @param color the color to use for the highlight.
     * @param level the level of the highlight.
     * @return the highlight.
     *
     * @throws BadLocationException if the line number is invalid.
     * @throws IOException if the file cannot be read.
     */
    public SourceViewHighlight addHighlight(URI fileURI, String group, int sourceLine, Color color,
                                            int level) throws BadLocationException, IOException {
        Tab tab = tabs.get(fileURI);

        if (tab == null || sourceLine < 0 || sourceLine >= tab.lineInformation.length) {
            throw new BadLocationException("Not a valid line number for " + fileURI, sourceLine);
        }

        int patchedLine = tab.translateSourceLineToPatchedLine(sourceLine);

        Range patchedRange = tab.calculatePatchedLineRangeFromLine(patchedLine);

        return addHighlightDirect(fileURI, group, sourceLine, patchedLine, patchedRange, color,
            level);
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
     * @param sourceLine the line to highlight.
     * @param color the color to use for the highlight.
     * @param level the level of the highlight.
     * @return the highlight.
     *
     * @throws BadLocationException if the line number is invalid.
     * @throws IOException if the file cannot be read.
     */
    public SourceViewHighlight addHighlight(URI fileURI, String group, int sourceLine, int startCol,
                                            int endCol, Color color, int level) throws BadLocationException, IOException {
        Tab tab = tabs.get(fileURI);

        if (tab == null || sourceLine < 0 || sourceLine >= tab.lineInformation.length) {
            throw new BadLocationException("Not a valid line number for " + fileURI, sourceLine);
        }

        int patchedLine = tab.translateSourceLineToPatchedLine(sourceLine);

        Range patchedRange = tab.calculatePatchedLineRangeFromLine(patchedLine, startCol, endCol);

        return addHighlightDirect(fileURI, group, sourceLine, patchedLine, patchedRange, color,
            level);
    }

    /**
     * <p>
     * Creates a new highlight (directly supplies patchedLine).
     * </p>
     *
     * @see addHighlight
     */
    public SourceViewHighlight addHighlightDirect(URI fileURI, String group, int sourceLine,
                                                  int patchedLine, Range patchedRange, Color color, int level)
        throws BadLocationException, IOException {
        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        if (!tab.highlights.containsKey(patchedLine)) {
            tab.highlights.put(patchedLine, new TreeSet<>(Collections.reverseOrder()));
        }

        SortedSet<SourceViewHighlight> highlights = tab.highlights.get(patchedLine);

        SourceViewHighlight highlight = new SourceViewHighlight(group, fileURI, sourceLine,
            patchedLine, patchedRange, color, level);
        highlights.add(highlight);

        tab.markTabComponent();

        tab.removeHighlights(patchedLine);
        tab.applyHighlights(patchedLine);

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
    public Set<SourceViewHighlight> addHighlightsForJMLStatement(URI fileURI, int firstLine,
             Color color, int level) throws BadLocationException, IOException {
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

        Set<SourceViewHighlight> result = new HashSet<>();

        for (int i = firstLine; i <= lastLine && tab != null; ++i) {
            result.add(addHighlight(fileURI, Tab.KEY_JML_HL, i, color, level));
        }

        return result;
    }

    public void removeHighlightsForJMLStatements() {
        removeHighlights(Tab.KEY_JML_HL);
    }

    /**
     * Moves an existing highlight to another line.
     *
     * @param oldHighlight the highlight to change.
     * @param newSourceLine the line to move the highlight to.
     *
     * @throws BadLocationException if the line number is invalid.
     */
    public SourceViewHighlight changeHighlight(SourceViewHighlight oldHighlight, int newSourceLine,
                                               int newPatchedLine, Range newPatchedRange) throws BadLocationException {
        URI fileURI = oldHighlight.getFileURI();
        int oldPatchedLine = oldHighlight.getPatchedLine();

        Tab tab = tabs.get(fileURI);

        if (tab == null || !tab.highlights.containsKey(oldPatchedLine)
                || !tab.highlights.get(oldPatchedLine).contains(oldHighlight)) {
            throw new IllegalArgumentException("highlight");
        }

        tab.removeHighlights(oldPatchedLine);
        tab.highlights.get(oldPatchedLine).remove(oldHighlight);
        tab.applyHighlights(oldPatchedLine);

        if (tab.highlights.get(oldPatchedLine).isEmpty()) {
            tab.highlights.remove(oldPatchedLine);
        }

        SourceViewHighlight newHighlight =
            new SourceViewHighlight(oldHighlight.group, oldHighlight.fileURI, newSourceLine,
                newPatchedLine, newPatchedRange, oldHighlight.color, oldHighlight.level);

        if (!tab.highlights.containsKey(newPatchedLine)) {
            tab.highlights.put(newPatchedLine, new TreeSet<>());
        }

        tab.highlights.get(newPatchedLine).add(newHighlight);
        tab.removeHighlights(newPatchedLine);
        tab.applyHighlights(newPatchedLine);

        fireHighlightsChanged();

        return newHighlight;
    }

    public List<SourceViewHighlight> listHighlights(String group) {
        return tabs.values().stream().flatMap(p -> p.highlights.values().stream())
            .flatMap(Collection::stream).filter(p -> p.group.equals(group))
            .collect(Collectors.toList());
    }

    public List<SourceViewHighlight> listHighlights(URI fileURI) {
        Tab tab = tabs.get(fileURI);

        if (tab == null) {
            return new ArrayList<>();
        }

        return tab.highlights.values().stream().flatMap(Collection::stream)
            .collect(Collectors.toList());
    }

    public List<SourceViewHighlight> listHighlights(URI fileURI, String group) {
        Tab tab = tabs.get(fileURI);

        if (tab == null) {
            return new ArrayList<>();
        }

        return tab.highlights.values().stream().flatMap(Collection::stream)
            .filter(p -> p.group.equals(group)).collect(Collectors.toList());
    }

    /**
     * Removes a highlight.
     *
     * @param highlight the highlight to remove.
     * @return {@code true} iff this {@code SourceView} previously contained the specified
     *         highlight.
     */
    public boolean removeHighlight(SourceViewHighlight highlight) {
        Tab tab = tabs.get(highlight.getFileURI());

        if (tab == null) {
            return false;
        }

        tab.removeHighlights(highlight.getPatchedLine());

        boolean result = tab.highlights.containsKey(highlight.getPatchedLine())
                && tab.highlights.get(highlight.getPatchedLine()).remove(highlight);
        highlight.setTag(null);

        if (result && tab.highlights.get(highlight.getPatchedLine()).isEmpty()) {
            tab.highlights.remove(highlight.getPatchedLine());
        } else {
            try {
                tab.applyHighlights(highlight.getPatchedLine());
            } catch (BadLocationException e) {
                // The locations of the highlights have already been checked
                // in addHighlight & changeHighlight, so no error can occur here.
                throw new AssertionError();
            }
        }

        tab.markTabComponent();

        return result;
    }

    public void removeHighlights(String group) {
        for (SourceViewHighlight h : listHighlights(group)) {
            removeHighlight(h);
        }
    }

    public void removeHighlights(URI fileUri, String group) {
        for (SourceViewHighlight h : listHighlights(fileUri, group)) {
            removeHighlight(h);
        }
    }

    public void addHighlightsChangedListener(HighlightsChangedListener listener) {
        listenerList.add(HighlightsChangedListener.class, listener);
    }

    public synchronized void fireHighlightsChanged() {
        for (HighlightsChangedListener listener : listenerList
            .getListeners(HighlightsChangedListener.class)) {
            listener.highlightsChanged();
        }
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

        final Proof selectedProof = mainWindow.getMediator().getSelectedProof();
        final ProofJavaSourceCollection sources =
            selectedProof != null ? selectedProof.lookup(ProofJavaSourceCollection.class) : null;

        for (URI fileURI : fileURIs) {
            if (addFile(fileURI)) {
                updateNecessary = true;
                if (sources != null) {
                    sources.addRelevantFile(fileURI);
                }
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
    private boolean isSymbExecHighlighted(Point point) {
        Tab tab = tabs.get(selectedFile);
        int pos = tab.textPane.viewToModel2D(point);

        for (SourceViewHighlight h : listHighlights(selectedFile, Tab.KEY_SYMB_EXEC_HL)) {
            // found matching highlight h: Is the mouse cursor inside the highlight?
            // we need < here, since viewToModel can not return a position after the last
            // char in a line
            if (h.patchedRange.start() <= pos && pos < h.patchedRange.end()) {
                return true;
            }
        }
        return false;
    }

    /**
     * Adds all files relevant to the currently selected node, closing all others
     */
    private void addFiles() {
        final Proof selectedProof = mainWindow.getMediator().getSelectedProof();
        final ProofJavaSourceCollection sources =
            selectedProof == null ? null : selectedProof.lookup(ProofJavaSourceCollection.class);

        if (sources == null) {
            return;
        }

        final ImmutableSet<URI> fileURIs = sources.getRelevantFiles();

        final Iterator<URI> it = tabs.keySet().iterator();
        while (it.hasNext()) {
            final URI fileURI = it.next();
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
        final Proof proof = mainWindow.getMediator().getSelectedProof();
        // quick fix: fileName could be null (see bug #1520)
        if (proof == null || fileURI == null || tabs.containsKey(fileURI)) {
            return false;
        } else {
            // try to load the file via the FileRepo
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
                            t.scrollToSourceLine(line, false);
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

    public void updateSymbExecHighlights() {
        Node currentNode = mainWindow.getMediator().getSelectedNode();

        if (currentNode != null) {
            // get PositionInfo of all symbEx nodes
            lines = constructLinesSet(currentNode);
            if (lines == null) return;
        }

        tabs.values().forEach(Tab::paintSymbExHighlights);
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
                formula -> formula.formula().execPostOrder(new Visitor<JTerm>() {

                    @Override
                    public boolean visitSubtree(JTerm visited) {
                        return visited.containsJavaBlockRecursive();
                    }

                    @Override
                    public void visit(JTerm visited) {}

                    @Override
                    public void subtreeLeft(JTerm subtreeRoot) {}

                    @Override
                    public void subtreeEntered(JTerm subtreeRoot) {
                        if (subtreeRoot.javaBlock() != null) {
                            JavaASTVisitor visitor =
                                new JavaASTVisitor(subtreeRoot.javaBlock().program(),
                                    mainWindow.getMediator().getServices()) {

                                    @Override
                                    protected void doDefaultAction(SourceElement el) {
                                        if (el instanceof MethodBodyStatement mb) {
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

    public void addInsertion(URI fileURI, SourceViewInsertion ins) throws IOException, BadLocationException {
        if (ins.Line <= 0) throw new BadLocationException("Line must be >= 0", ins.Line);

        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        tab.addInsertions(ins);

        tab.refreshInsertions();
    }

    public void addInsertions(URI fileURI, List<SourceViewInsertion> inslist) throws IOException, BadLocationException {
        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        for (SourceViewInsertion ins : inslist) {
            if (ins.Line <= 0) throw new BadLocationException("Line must be >= 0", ins.Line);
            tab.addInsertions(ins);
        }

        tab.refreshInsertions();
    }

    public void removeInsertion(URI fileURI, SourceViewInsertion ins)
        throws IOException, BadLocationException {
        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        tab.removeInsertion(ins);

        tab.refreshInsertions();
    }

    public void clearInsertion(URI fileURI, String group) throws IOException, BadLocationException {
        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        for (SourceViewInsertion ins : tab.insertions.stream().filter(p -> p.Group.equals(group))
            .collect(Collectors.toList())) {
            tab.removeInsertion(ins);
        }

        tab.refreshInsertions();
    }

    public void clearAllInsertion(URI fileURI) throws IOException, BadLocationException {
        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        for (SourceViewInsertion ins : new ArrayList<>(tab.insertions)) {
            tab.removeInsertion(ins);
        }

        tab.refreshInsertions();
    }

    public List<SourceViewInsertion> listInsertion(String group) {
        return tabs.values().stream().flatMap(p -> p.insertions.stream())
            .filter(p -> p.Group.equals(group)).collect(Collectors.toList());
    }

    public List<SourceViewInsertion> listInsertion(URI fileURI, String group) throws IOException {
        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        return tab.insertions.stream().filter(p -> p.Group.equals(group))
            .collect(Collectors.toList());
    }

    public List<SourceViewInsertion> listInsertion(URI fileURI) throws IOException {
        openFile(fileURI);

        Tab tab = tabs.get(fileURI);

        return new ArrayList<>(tab.insertions);
    }

    public void addInsertionChangedListener(InsertionChangedListener listener) {
        listenerList.add(InsertionChangedListener.class, listener);
    }

    public synchronized void fireInsertionChanged() {
        for (InsertionChangedListener listener : listenerList
            .getListeners(InsertionChangedListener.class)) {
            listener.insertionsChanged();
        }
    }

    public void removeSourceClickedListener(SourceClickedListener listener) {
        listenerList.remove(SourceClickedListener.class, listener);
    }

    public void addSourceClickedListener(SourceClickedListener listener) {
        listenerList.add(SourceClickedListener.class, listener);
    }

    public synchronized void fireSourceClicked(@Nullable SourceViewInsertion ins, MouseEvent evt) {
        for (SourceClickedListener listener : listenerList.getListeners(SourceClickedListener.class)) {
            listener.sourceClicked(ins, evt);
        }
    }

    /**
     * Joins all PositionInfo objects of the given SourceElement and its children.
     *
     * @param se the given SourceElement
     * @return a new PositionInfo starting at the minimum of all the contained positions and ending
     *         at the maximum position
     */
    private static PositionInfo joinPositionsRec(SourceElement se) {
        if (se instanceof NonTerminalProgramElement ntpe) {
            // TODO: additional elements, e.g. code inside if
            if (se instanceof If || se instanceof Then || se instanceof Else) {
                return PositionInfo.UNDEFINED;
            }

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
        return "Show Postcondition/Modifiable";
    }

    public URI getSelectedFile() {
        Tab tab = tabPane.getSelectedTab();
        if (tab == null) {
            return null;
        }
        return tab.absoluteFileName;
    }

    public boolean hasFile(URI fileURI) {
        return tabs.containsKey(fileURI);
    }

    public void refreshInsertions() {
        for (var tab: tabs.values()) {
            tab.refreshInsertions();
        }
    }

    public void repaintInsertion(SourceViewInsertion ins) {
        for (var tab: tabs.values()) {
            tab.repaintInsertion(ins);
        }
    }

    public void setErrorDisplay(Color background, String text) {
        errorText.setText(text);
        errorCenter.setBackground(background);

        if (text.isEmpty()) {
            remove(errorPane);
            add(tabPane, BorderLayout.CENTER);
            revalidate();
            repaint();
        } else {
            remove(tabPane);
            add(errorPane, BorderLayout.CENTER);
            revalidate();
            repaint();
        }
    }

    public void setInfoDisplay(Color background, String text) {
        SwingUtilities.invokeLater(() -> {
            infoText.setText("<html>"+text.replaceAll("\n", "<br/>")+"</html>");
            infoCenter.setBackground(background);

            if (text.isEmpty()) {
                infoWrap.setVisible(false);
            } else {
                infoWrap.setVisible(true);
            }
        });
    }

    public int getScrollPosition() {
        return this.tabPane.getSelectedTab().getVerticalScrollBar().getValue();
    }

    public void setScrollPosition(int v) {
        this.tabPane.getSelectedTab().getVerticalScrollBar().setValue(v);
    }

    public boolean scrollToActiveStatement() {
        var tab = this.tabPane.getSelectedTab();
        if (lines.size() > 0) {
            var line = lines.getFirst().second.getEndPosition().line();
            return tab.scrollToSourceLine(line, true);
        }
        return false;
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

        private final static String KEY_SELECTION_HL =
            "de.uka.ild.key.gui.SourceView.Tab::selection_hl";
        private final static String KEY_JML_HL = "de.uka.ild.key.gui.SourceView.Tab::jml_hl";
        private final static String KEY_SYMB_EXEC_HL =
            "de.uka.ild.key.gui.SourceView.Tab::symb_exec";

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

                if (isSymbExecHighlighted(mouseEvent.getPoint())) {
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
        private SourceViewHighlight selectionHL;

        /**
         * The file's content with tabs replaced by spaces and with Insertions included
         */
        private String patchedSource;

        private final HashMap<Integer, Integer> cacheTranslateToSourcePos = new HashMap<>();
        private final HashMap<Integer, Integer> cacheTranslateToPatchedPos = new HashMap<>();
        private final HashMap<Integer, Integer> cacheTranslatePosToSourceLine = new HashMap<>();
        private final HashMap<Integer, Integer> cacheTranslatePosToPatchedLine = new HashMap<>();

        /**
         * Maps line numbers to highlights.
         */
        private final Map<Integer, SortedSet<SourceViewHighlight>> highlights = new HashMap<>();

        /** Extra lines dynamically added into the view */
        private final List<SourceViewInsertion> insertions = new ArrayList<>();

        private final List<MouseListener> registeredListener = new ArrayList<>();
        private final List<MouseMotionListener> registeredMotionListener = new ArrayList<>();

        /**
         * The JavaDocument shown in this tab.
         */
        private final SourceHighlightDocument doc =
            new SourceHighlightDocument(new JavaJMLEditorLexer());

        private Tab(URI fileURI, InputStream stream) {
            this.absoluteFileName = fileURI;
            this.simpleFileName = extractFileName(fileURI);

            String fsource = "";

            try {
                String text = IOUtil.readFrom(stream);
                if (!text.isEmpty()) {
                    fsource = replaceTabs(text);
                } else {
                    fsource = "[SOURCE COULD NOT BE LOADED]";
                }
            } catch (IOException e) {
                fsource = "[SOURCE COULD NOT BE LOADED]";
                LOGGER.debug("Unknown IOException!", e);
            }

            //initLineInfo();

            initTextPane(fsource);

            JPanel nowrap = new JPanel(new BorderLayout());
            nowrap.add(textPane);
            setViewportView(nowrap);
            setHorizontalScrollBarPolicy(HORIZONTAL_SCROLLBAR_AS_NEEDED);
            setVerticalScrollBarPolicy(VERTICAL_SCROLLBAR_AS_NEEDED);

            // increase unit increment (for faster scrolling)
            getVerticalScrollBar().setUnitIncrement(30);
            getHorizontalScrollBar().setUnitIncrement(30);

            // add Line numbers to each Scrollview
            TextLineNumber tln = new TextLineNumber(textPane, 1);
            tln.setUpdateFont(true);
            setRowHeaderView(tln);

            initLineNumbers();
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

        private void initLineInfo(String fsource) {
            try {
                InputStream inStream = new ByteArrayInputStream(fsource.getBytes(StandardCharsets.UTF_8));
                lineInformation = IOUtil.computeLineInformation(inStream);
            } catch (IOException e) {
                LOGGER.debug("Error while computing line information from {}", absoluteFileName, e);
            }
        }

        private void initTextPane(String fsource) {
            for (MouseListener l: registeredListener) {
                textPane.removeMouseListener(l);
            }
            registeredListener.clear();

            for (MouseMotionListener l: registeredMotionListener) {
                textPane.removeMouseMotionListener(l);
            }
            registeredMotionListener.clear();

            this.cacheTranslateToSourcePos.clear();
            this.cacheTranslateToPatchedPos.clear();
            this.cacheTranslatePosToSourceLine.clear();
            this.cacheTranslatePosToPatchedLine.clear();

            // insert source code into text pane
            try {
                this.source = fsource;
                this.patchedSource = patchSourceWithInsertions(fsource, insertions);

                initLineInfo(fsource);


                // We use the same font as in SequentView for consistency.
                textPane.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
                textPane.setToolTipText("");
                textPane.setEditable(false);
                MouseMotionAdapter mml = new MouseMotionAdapter() {
                    @Override
                    public void mouseMoved(MouseEvent mouseEvent) {
                        if (isSymbExecHighlighted(mouseEvent.getPoint())) {
                            textPane.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
                            return;
                        }

                        SourceViewInsertion ins =
                            getInsertionAtPatchedPos(textPane.viewToModel(mouseEvent.getPoint()));
                        if (ins != null && ins.hasClickListener()) {
                            textPane.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
                            return;
                        }

                        textPane.setCursor(Cursor.getDefaultCursor());
                    }
                };
                textPane.addMouseMotionListener(mml);

                registeredMotionListener.add(mml);

                JavaDocument doc = new JavaDocument();
                textPane.setDocument(doc);
                doc.insertString(0, this.source, new SimpleAttributeSet());

                String lineBreak = getLineBreakSequence();
                for (SourceViewInsertion ins : insertions.stream()
                    .sorted(Comparator.comparingInt(a -> -a.Line))
                    .collect(Collectors.toList())) {
                    int idx = ins.Line - 1;
                    if (idx < 0 || idx >= lineInformation.length)
                        continue;

                    int pos = lineInformation[idx].getOffset();

                    doc.insertExtraString(pos, ins.getCleanText() + lineBreak,
                        ins.getStyleAttrbuteSet());
                }
            } catch (IOException | BadLocationException e) {
                throw new AssertionError();
            }

            // add a listener to highlight the line currently pointed to
            MouseMotionListener mml2 = new MouseMotionListener() {
                @Override
                public void mouseMoved(MouseEvent e) {
                    synchronized (SourceView.this) {
                        updateSelectionHighlight(e.getPoint());
                    }
                }

                @Override
                public void mouseDragged(MouseEvent e) {}
            };
            textPane.addMouseMotionListener(mml2);
            registeredMotionListener.add(mml2);

            MouseListener mml3 = new MouseAdapter() {
                @Override
                public void mouseExited(MouseEvent e) {
                    synchronized (SourceView.this) {
                        updateSelectionHighlight(null);
                    }
                }

                @Override
                public void mouseEntered(MouseEvent e) {
                    synchronized (SourceView.this) {
                        updateSelectionHighlight(e.getPoint());
                    }
                }
            };
            textPane.addMouseListener(mml3);
            registeredListener.add(mml3);

            MouseAdapter adapter = new TextPaneMouseAdapter(this, textPane, lineInformation, absoluteFileName);

            textPane.addMouseListener(adapter);
            registeredListener.add(adapter);

            textPane.addMouseMotionListener(adapter);
            registeredMotionListener.add(adapter);
        }

        private void initLineNumbers() {

            List<SourceViewInsertion> ins = insertions.stream()
                .sorted(Comparator.comparingInt(a -> a.Line)).collect(Collectors.toList());


            int[] skips = new int[ins.size()];

            for (int i = 0; i < ins.size(); i++) {
                skips[i] = ins.get(i).Line + i;
            }

            // add Line numbers to each Scrollview
            TextLineNumber tln = new TextLineNumber(textPane, 1, skips);
            setRowHeaderView(tln);
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

        /*
        private void initSelectionHL() {
            try {
                selectionHL = addHighlight(absoluteFileName, 1,
                    CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR.get(), Integer.MAX_VALUE - 1);
            } catch (BadLocationException | IOException e) {
                LOGGER.debug("Caught exception!", e);
            }
        }*/

        private void removeHighlights(int patchedLine) {
            SortedSet<SourceViewHighlight> set = highlights.get(patchedLine);

            if (set == null) {
                return;
            }

            for (SourceViewHighlight highlight : set) {
                if (highlight.getTag() != null) {
                    textPane.getHighlighter().removeHighlight(highlight.getTag());
                    highlight.setTag(null);
                }
            }

            SourceView.this.fireHighlightsChanged();
        }

        private void applyHighlights(int patchedLine) throws BadLocationException {
            SortedSet<SourceViewHighlight> set = highlights.get(patchedLine);

            if (set != null && !set.isEmpty()) {
                for (SourceViewHighlight highlight : set) {
                    //Range range = calculateLineRange(textPane,
                    //    lineInformation[highlight.getLine() - 1].getOffset());
                    Range range = highlight.patchedRange;

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

        private void reapplyAllHighlights() throws BadLocationException {

            textPane.getHighlighter().removeAllHighlights();

            for(int patchedLine: highlights.keySet()) {
                SortedSet<SourceViewHighlight> set = highlights.get(patchedLine);

                if (set != null && !set.isEmpty()) {
                    for (SourceViewHighlight highlight : set) {
                        Range range = highlight.patchedRange;

                        Color c = highlight.getColor();
                        int alpha = set.size() == 1 ? c.getAlpha() : 256 / set.size();
                        Color color = new Color(c.getRed(), c.getGreen(), c.getBlue(), alpha);

                        highlight.setTag(textPane.getHighlighter().addHighlight(range.start(),
                            range.end(), new DefaultHighlightPainter(color)));
                    }
                }

            }

            // LinePainter handles full-length backgrounds (highlight whole line) of insertions
            textPane.getHighlighter().addHighlight(0, 0, new LinePainter());

            textPane.revalidate();
            textPane.repaint();
        }

        /**
         * Paints the highlights for symbolically executed lines. The most recently executed line is
         * highlighted with a different color.
         */
        private void paintSymbExHighlights() {
            SourceView.this.removeHighlights(getSelectedFile(), KEY_SYMB_EXEC_HL);

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
                            addHighlight(absoluteFileName, KEY_SYMB_EXEC_HL, line,
                                MOST_RECENT_HIGHLIGHT_COLOR.get(), 0);
                        } else if (line != mostRecentLine) {
                            addHighlight(absoluteFileName, KEY_SYMB_EXEC_HL, line,
                                NORMAL_HIGHLIGHT_COLOR.get(), 0);
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
        private void updateSelectionHighlight(Point p) {
            if (p == null) {
                SourceView.this.removeHighlights(absoluteFileName, KEY_SELECTION_HL);
                return;
            }
            if (listHighlights(absoluteFileName, KEY_SELECTION_HL).size() > 1) {
                SourceView.this.removeHighlights(absoluteFileName, KEY_SELECTION_HL);
            }

            var selectionHL = listHighlights(absoluteFileName, KEY_SELECTION_HL).stream()
                .findFirst().orElse(null);

            try {
                int patchedPos = textPane.viewToModel(p);

                SourceViewInsertion ins = getInsertionAtPatchedPos(patchedPos);
                if (ins != null) {

                    int patchedLine = translatePatchedPosToPatchedLine(patchedPos);
                    Range patchedRange = calculatePatchedLineRange(patchedPos);

                    if (selectionHL == null) {
                        try {
                            addHighlightDirect(absoluteFileName, KEY_SELECTION_HL, -1, patchedLine,
                                patchedRange, CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR.get(),
                                Integer.MAX_VALUE - 1);
                        } catch (BadLocationException | IOException e) {
                            LOGGER.debug("Caught exception!", e);
                        }
                    } else {
                        changeHighlight(selectionHL, -1, patchedLine, patchedRange);
                    }

                    return;
                }

                int sourceLine = translatePatchedPosToSourceLine(patchedPos);
                int patchedLine = translatePatchedPosToPatchedLine(patchedPos);
                Range patchedRange = calculatePatchedLineRange(patchedPos);

                if (selectionHL == null) {
                    try {
                        addHighlight(absoluteFileName, KEY_SELECTION_HL, sourceLine,
                            CurrentGoalView.DEFAULT_HIGHLIGHT_COLOR.get(), Integer.MAX_VALUE - 1);
                    } catch (BadLocationException | IOException e) {
                        LOGGER.debug("Caught exception!", e);
                    }
                } else {
                    changeHighlight(selectionHL, sourceLine, patchedLine, patchedRange);
                }

            } catch (BadLocationException e) {
                LOGGER.debug("Caught exception!", e);
            }
        }

        private int posToLine(int pos) {
            return textPane.getDocument().getDefaultRootElement().getElementIndex(pos) + 1;
        }

        private boolean scrollToSourceLine(int sourceLine, boolean center) {
            int offs = lineInformation[sourceLine].getOffset();
            offs = translateToPatchedPos(offs);

            if (!center) {

                textPane.setCaretPosition(offs);
                return true;

            } else {

                Container container = SwingUtilities.getAncestorOfClass(JViewport.class, textPane);
                if (container == null) return false;

                try
                {
                    Rectangle r = textPane.modelToView(offs);
                    JViewport viewport = (JViewport)container;

                    int extentHeight = viewport.getExtentSize().height;
                    int viewHeight = viewport.getViewSize().height;

                    int y = Math.max(0, r.y - (extentHeight / 2));
                    y = Math.min(y, viewHeight - extentHeight);

                    viewport.setViewPosition(new Point(0, y));

                    return true;
                }
                catch(BadLocationException ble) {
                    return false;
                }
            }
        }


        private void dispose() {
            if (doc != null) {
                // TODO: WP:
                //doc.dispose();
            }
        }

        /**
         * Called after insertions array changed
         */
        public void refreshInsertions() {

            initTextPane(this.source);

            initLineNumbers();

            textPane.revalidate();
            textPane.repaint();
        }

        /**
         * Calculates the range of actual text (not whitespace) in the line containing the given
         * position.
         *
         * @param patchedPos the position to check (in displayed content)
         * @return the range of text (may be empty if there is just whitespace in the line)
         */
        private Range calculatePatchedLineRange(int patchedPos) {
            String text = this.patchedSource;

            // find line end
            int end = text.indexOf('\n', patchedPos);
            end = end == -1 ? text.length() : end; // last line?

            // find line start
            int start = text.lastIndexOf('\n', patchedPos - 1); // TODO: different line endings?
            start = start == -1 ? 0 : start; // first line?

            // ignore whitespace at the beginning of the line
            while (start < text.length() && start < end
                && Character.isWhitespace(text.charAt(start))) {
                start++;
            }

            return new Range(start, end);
        }

        /**
         * Calculates the range of actual text (not whitespace) in the line containing the given
         * position.
         *
         * @param patchedLine the line to check (in displayed content)
         * @return the range of text (may be empty if there is just whitespace in the line)
         */
        private Range calculatePatchedLineRangeFromLine(int patchedLine) {
            return calculatePatchedLineRangeFromLine(patchedLine, true);
        }

        private Range calculatePatchedLineRangeFromLine(int patchedLine,
                                                        boolean skipLeadingSpaces) {

            int start = 0;

            for (int i = 1; i < patchedLine; i++) {
                int next = patchedSource.indexOf('\n', start + 1);
                if (next == -1) {
                    if (i == patchedLine - 1) { // last line
                        break;
                    }

                    return new Range(0, 0);
                }
                start = next;
            }

            int end = patchedSource.indexOf('\n', start + 1);
            if (end == -1) {
                end = patchedSource.length();
            }

            if (skipLeadingSpaces) {
                // ignore whitespace at the beginning of the line
                while (start < patchedSource.length() && start < end
                    && Character.isWhitespace(patchedSource.charAt(start))) {
                    start++;
                }
            }

            return new Range(start, end);
        }


        public Range calculatePatchedLineRangeFromLine(int patchedLine, int startCol, int endCol) {
            Range fullRange = calculatePatchedLineRangeFromLine(patchedLine, false);

            int start = fullRange.start();
            int end = fullRange.end();

            startCol += start + 1;
            endCol += start + 1;

            if (startCol > start) {
                start = Math.min(startCol, fullRange.end());
            }
            if (endCol < end) {
                end = Math.max(endCol, fullRange.start());
            }

            if (start > end) {
                end = start;
            }

            return new Range(start, end);
        }

        /**
         * Get the used linebreaks (\n | \r\n) in this document
         */
        private String getLineBreakSequence() {
            if (source.contains("\r\n")) {
                return "\r\n";
            }
            return "\n";
        }

        /**
         * Add Insertions to a string
         */
        private String patchSourceWithInsertions(String source,
                                                 List<SourceViewInsertion> insertions) throws IOException {
            InputStream inStream = new ByteArrayInputStream(source.getBytes());
            lineInformation = IOUtil.computeLineInformation(inStream);

            String lineBreak = getLineBreakSequence();

            for (SourceViewInsertion ins : insertions.stream()
                .sorted(Comparator.comparingInt(a -> -a.Line)).collect(Collectors.toList())) {

                int idx = ins.Line - 1;

                if (idx < 0 || idx >= lineInformation.length)
                    continue;

                int pos = lineInformation[idx].getOffset();

                source = source.substring(0, pos) + ins.getCleanText() + lineBreak
                    + source.substring(pos);
            }

            return source;

        }

        /**
         * get the insertion at this (patched) position (or null if none)
         */
        private SourceViewInsertion getInsertionAtPatchedPos(int patchedPos) {

            int patchedLine = 1 + (int) Pattern.compile("\r?\n")
                .matcher(this.patchedSource.substring(0, patchedPos)).results().count();

            ArrayList<SourceViewInsertion> rev = new ArrayList<>(insertions);
            Collections.reverse(rev);

            int offset = 0;
            for (SourceViewInsertion ins : rev.stream().sorted(Comparator.comparingInt(a -> a.Line))
                .collect(Collectors.toList())) {

                int idx = ins.Line - 1;
                if (idx < 0 || idx >= lineInformation.length)
                    continue;

                if (offset + ins.Line == patchedLine)
                    return ins;

                offset++;
            }

            return null;
        }


        private Range calculatePatchedPosFromInsertion(SourceViewInsertion svi) {
            int idx = svi.Line - 1;
            if (idx < 0 || idx >= lineInformation.length) return null;

            String lineBreak = getLineBreakSequence();

            var inf = lineInformation[idx];

            var offset1 = inf.getOffset();

            ArrayList<SourceViewInsertion> rev = new ArrayList<>(insertions);
            Collections.reverse(rev);

            var offset2 = rev.stream().
                sorted(Comparator.comparingInt(a -> a.Line)).
                takeWhile(p -> p != svi).
                mapToInt(p -> p.getCleanText().length()+lineBreak.length()).
                sum();

            return new Range(offset1 + offset2, svi.getCleanText().length());
        }

        /**
         * Translates an offset in the displayed document into a line-number in the source fule
         * (must undo insertions)
         */
        private int translatePatchedPosToSourceLine(int patchedPos) {
            if (this.cacheTranslatePosToSourceLine.containsKey(patchedPos)) {
                return this.cacheTranslatePosToSourceLine.get(patchedPos);
            }

            patchedPos = translateToSourcePos(patchedPos);
            int result = 1 + (int) Pattern.compile("\r?\n")
                .matcher(this.source.substring(0, Math.min(patchedPos, this.source.length()))).results().count();

            this.cacheTranslatePosToSourceLine.put(patchedPos, result);

            return result;
        }

        /**
         * Translates an offset in the displayed document into an offset in the source fule (must
         * undo insertions)
         */
        private int translatePatchedPosToPatchedLine(int patchedPos) {
            if (this.cacheTranslatePosToPatchedLine.containsKey(patchedPos)) {
                return this.cacheTranslatePosToPatchedLine.get(patchedPos);
            }

            int result = 1 + (int) Pattern.compile("\r?\n")
                .matcher(this.patchedSource.substring(0, patchedPos)).results().count();

            this.cacheTranslatePosToPatchedLine.put(patchedPos, result);

            return result;
        }

        /**
         * Translates an offset in the source file into an offset in the displayed Document (must
         * skip Insertions)
         */
        public int translateToPatchedPos(int sourcePos) {
            if (this.cacheTranslateToPatchedPos.containsKey(sourcePos)) {
                return this.cacheTranslateToPatchedPos.get(sourcePos);
            }

            String lineBreak = getLineBreakSequence();

            int sourceLine = 1;
            for (LineInformation li : lineInformation) {
                if (li.getOffset() < sourcePos) {
                    sourceLine++;
                }
            }

            int offset = 0;
            for (SourceViewInsertion ins : insertions.stream()
                .sorted(Comparator.comparingInt(a -> a.Line)).collect(Collectors.toList())) {
                if (ins.Line <= sourceLine) {
                    offset += ins.getCleanText().length() + lineBreak.length();
                }
            }

            int result = sourcePos + offset;

            cacheTranslateToPatchedPos.put(sourcePos, result);

            return result;
        }

        /**
         * Translates an offset in displayed document into an offset in the source file (must undo
         * Insertions)
         */
        public int translateToSourcePos(int patchedPos) {
            if (this.cacheTranslateToSourcePos.containsKey(patchedPos)) {
                return this.cacheTranslateToSourcePos.get(patchedPos);
            }

            int lineInPatched = 1 + (int) Pattern.compile("\r?\n")
                .matcher(this.patchedSource.substring(0, patchedPos)).results().count();

            String lineBreak = getLineBreakSequence();

            int result = patchedPos;

            int offset = 0;
            for (SourceViewInsertion ins : insertions.stream()
                .sorted(Comparator.comparingInt(a -> a.Line)).collect(Collectors.toList())) {

                int idx = ins.Line - 1;
                if (idx < 0 || idx >= lineInformation.length)
                    continue;
                if (offset + ins.Line > lineInPatched)
                    break;

                offset++;
                result -= ins.getCleanText().length() + lineBreak.length();
            }

            cacheTranslateToSourcePos.put(patchedPos, result);

            return result;

        }

        /**
         * Translates a line in the souce into a line in the displayed content (must add Insertion
         * offsets)
         */
        public int translateSourceLineToPatchedLine(int sourceLine) {

            int offset = (int) insertions.stream().filter(p -> p.Line < sourceLine).count();

            return sourceLine + offset;

        }

        /**
         * Add a new insertion (mus move existign highlights)
         */
        public void addInsertions(SourceViewInsertion ins) throws BadLocationException {
            this.insertions.add(ins);

            // adjust existing highlights

            String lineBreak = getLineBreakSequence();

            int patchedLine = translateSourceLineToPatchedLine(ins.Line);

            int addLen = ins.getCleanText().length() + lineBreak.length();

            batchUpdateHighlights(-1, patchedLine, 1, addLen);

            SourceView.this.fireInsertionChanged();
        }


        /**
         * Remove an existing insertion (mus move existign highlights)
         */
        public void removeInsertion(SourceViewInsertion ins) throws BadLocationException {
            if (!this.insertions.remove(ins)) {
                return;
            }

            // adjust existing highlights

            String lineBreak = getLineBreakSequence();

            int patchedLine = translateSourceLineToPatchedLine(ins.Line);

            int remLen = ins.getCleanText().length() + lineBreak.length();

            batchUpdateHighlights(patchedLine, patchedLine, -1, -remLen);

            SourceView.this.fireInsertionChanged();
        }

        /**
         * Update the position of all existing highlights
         *
         * @param remLine remove line at this (patched) position
         * @param startLine only update lines with (patched) line >= (patched)startLine
         * @param lineDelta change the patchedLine attribute by this value
         * @param rangeDelta change the patchedRange attribute by this value
         */
        private void batchUpdateHighlights(int remLine, int startLine, int lineDelta, int rangeDelta) throws BadLocationException {

            // deep-copy highlights map, because we want to modify it in the following loop
            var data = highlights.entrySet().stream()
                .map(p -> new Tuple<>(p.getKey(), new HashSet<>(p.getValue())))
                .sorted(Comparator.comparingInt(a -> -a.getA())).collect(Collectors.toList());

            for (Tuple<Integer, HashSet<SourceViewHighlight>> entry : data) {
                for (SourceViewHighlight hl : entry.getB()) {
                    if (remLine >= 0 && hl.patchedLine == remLine) {

                        highlights.get(entry.getA()).remove(hl);

                    } else if (hl.patchedLine >= startLine) {

                        SourceViewHighlight hlNew = new SourceViewHighlight(hl.group, hl.fileURI,
                            hl.sourceLine, hl.patchedLine + lineDelta,
                            new Range(hl.patchedRange.start() + rangeDelta,
                                hl.patchedRange.end() + rangeDelta),
                            hl.color, hl.level);

                        highlights.get(entry.getA()).remove(hl);

                        if (!highlights.containsKey(hlNew.patchedLine)) {
                            highlights.put(hlNew.patchedLine,
                                new TreeSet<>(Collections.reverseOrder()));
                        }
                        highlights.get(hlNew.patchedLine).add(hlNew);

                    }
                }

                if (highlights.get(entry.getA()).isEmpty()) {
                    highlights.remove(entry.getA());
                }
            }

            reapplyAllHighlights();

            SourceView.this.fireHighlightsChanged();
        }

        public void repaintInsertion(SourceViewInsertion svi) {
            String lineBreak = getLineBreakSequence();
            JavaDocument doc = (JavaDocument)textPane.getDocument();

            var extraOffset = 0;

            var insList = insertions.stream()
                .sorted(Comparator.comparingInt(a -> -a.Line))
                .collect(Collectors.toList());
            Collections.reverse(insList);

            for (SourceViewInsertion ins : insList) {
                int idx = ins.Line - 1;
                if (idx < 0 || idx >= lineInformation.length){
                    continue;
                }

                if (svi == null || svi == ins) {
                    int pos = lineInformation[idx].getOffset() + extraOffset;
                    doc.setCharacterAttributes(pos, ins.getCleanText().length(), ins.getStyleAttrbuteSet(), true);
                }

                extraOffset += (ins.getCleanText() + lineBreak).length();
            }
        }

        public class LinePainter implements Highlighter.HighlightPainter {
            @Override
            public void paint(Graphics g, int p0, int p1, Shape bounds, JTextComponent c) {
                try
                {
                    for (var svi : insertions.stream().sorted(Comparator.comparingInt(a -> a.Line)).collect(Collectors.toList())) {
                        if (svi.LineColor != null) {
                            Range svirange = calculatePatchedPosFromInsertion(svi);
                            if (svirange != null) {
                                Rectangle r = c.modelToView(svirange.start()+1);
                                g.setColor( svi.LineColor );
                                g.fillRect(0, r.y, c.getWidth(), r.height); // highlight whole line
                                //g.fillRect(r.x, r.y, 10, r.height);
                            }
                        }
                    }
                }
                catch(BadLocationException e) {
                    System.err.println(e.toString());
                }
            }
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
        /**
         * The source Tab
         */
        final Tab tab;

        private SourceViewInsertion hoveredInsertion = null;

        private TextPaneMouseAdapter(Tab tab, JTextPane textPane, LineInformation[] li,
                                     URI fileURI) {
            this.textPane = textPane;
            this.li = li;
            this.fileURI = fileURI;
            this.tab = tab;
        }

        @Override
        public void mouseClicked(MouseEvent e) {
            final int patchedPos = textPane.viewToModel2D(e.getPoint());
            int patchedLine = tab.translatePatchedPosToSourceLine(patchedPos);

            if (isSymbExecHighlighted(e.getPoint())) {
                onClickSymbExec(patchedPos, patchedLine);
            }

            SourceViewInsertion ins = tab.getInsertionAtPatchedPos(patchedPos);
            if (ins != null) {
                if (e.getButton() == MouseEvent.BUTTON1) {
                    ins.triggerClickListener(e);
                } else if (e.getButton() == MouseEvent.BUTTON3) {
                    ins.triggerRightClickListener(e);
                }
            }

            fireSourceClicked(ins, e);
        }

        @Override
        public void mouseMoved(MouseEvent e) {
            int patchedPos = textPane.viewToModel(e.getPoint());

            SourceViewInsertion ins = tab.getInsertionAtPatchedPos(patchedPos);
            if (ins != null) {
                if (hoveredInsertion == ins) {
                    ins.triggerMouseMoveListener(e);
                } else if (hoveredInsertion != null) {
                    hoveredInsertion.triggerMouseLeaveListener(e);
                    ins.triggerMouseEnterListener(e);
                } else {
                    ins.triggerMouseEnterListener(e);
                }

                hoveredInsertion = ins;
            } else {
                if (hoveredInsertion != null) {
                    hoveredInsertion.triggerMouseLeaveListener(e);
                }
                hoveredInsertion = null;
            }
        }

        @Override
        public void mouseExited(MouseEvent e) {
            if (hoveredInsertion != null) {
                hoveredInsertion.triggerMouseLeaveListener(e);
            }
            hoveredInsertion = null;
        }

        private void onClickSymbExec(int patchedPos, int patchedLine) {

            // jump in proof tree (get corresponding node from list)
            Node n = null;
            for (Pair<Node, PositionInfo> p : lines) {
                if (p.second.getStartPosition().line() == patchedLine
                    && fileURI.equals(p.second.getURI().orElse(null))) {
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
