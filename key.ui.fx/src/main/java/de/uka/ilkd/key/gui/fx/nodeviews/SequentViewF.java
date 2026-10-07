/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.TreeSet;
import java.util.function.Consumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javafx.geometry.Insets;
import javafx.geometry.Point2D;
import javafx.scene.control.Button;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.control.Tooltip;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.shape.HLineTo;
import javafx.scene.shape.LineTo;
import javafx.scene.shape.MoveTo;
import javafx.scene.shape.PathElement;
import javafx.scene.shape.VLineTo;
import javafx.scene.text.Font;
import javafx.scene.text.HitInfo;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;

import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.IllegalRegexException;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SearchSequentPrintFilter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;
import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * JavaFX version of the sequent view, the counter-part of
 * {@code de.uka.ilkd.key.gui.nodeviews.SequentView} (a Swing {@code JEditorPane} with HTML
 * content) in the module {@code key.ui}.
 * <p>
 * <b>Milestone M2.</b> The layout is a {@link BorderPane} like the Swing view's panel: the
 * sequent in the center, the search bar at the bottom (hidden until requested, Swing
 * {@code SequentViewSearchBar}). The rendering pipeline reuses the UI-agnostic pretty-printer of
 * {@code key.core}: {@link SequentViewLogicPrinter} produces the printed sequent string together
 * with an {@link InitialPositionTable} that maps character indexes to {@link PosInSequent}s. The
 * string is rendered as {@link Text} runs inside a {@link TextFlow}; mouse clicks are mapped with
 * {@link TextFlow#getHitInfo} back to a character index and hence to a {@link PosInSequent} -- no
 * HTML, no AWT.
 * <p>
 * <b>Search</b> (Swing {@code SequentViewSearchBar}): the query (with the RegExp toggle switching
 * between literal and regular-expression matching, same pattern semantics as
 * {@code SearchSequentPrintFilter.createPattern}: an all-lowercase query matches
 * case-insensitively, whitespace runs match line breaks) highlights all matches in the rendered
 * text; Prev/Next cycle the current match (stronger styling) and scroll it into view. Open with
 * {@code Ctrl+Shift+F}, close with {@code Escape}. The Swing modes that change the printed text
 * (Hide, Regroup — implemented as sequent print filters) are deferred to the print-filter chunk.
 * <p>
 * Deliberately deferred to later chunks: syntax highlighting of the printed terms, hover
 * tooltips, update highlighting (highlighting the formulas changed by a rule application),
 * sequent hiding, mediator wiring (shared {@code NotationInfo} and term label visibility), and
 * translucent rectangle highlights behind the matches (the search currently colors the matched
 * text; inline background spans of a {@link TextFlow} cannot split across wrapped lines).
 */
public class SequentViewF extends BorderPane {

    private static final Logger LOGGER = LoggerFactory.getLogger(SequentViewF.class);

    /**
     * Visible term labels of the spike: none. The real view feeds this from the mediator's term
     * label visibility manager.
     */
    private static final VisibleTermLabels NO_VISIBLE_TERM_LABELS = new VisibleTermLabels() {
        @Override
        public boolean contains(TermLabel label) {
            return false;
        }

        @Override
        public boolean contains(Name name) {
            return false;
        }
    };

    private static final KeyCombination OPEN_SEARCH =
        new KeyCodeCombination(KeyCode.F, KeyCombination.CONTROL_DOWN, KeyCombination.SHIFT_DOWN);

    private final ScrollPane scrollPane = new ScrollPane();
    private final TextFlow textFlow = new TextFlow();

    private final HBox searchBar = new HBox(4);
    private final TextField searchField = new TextField();
    private final ToggleButton regexToggle = new ToggleButton("RegExp");

    private final IdentitySequentPrintFilter filter = new IdentitySequentPrintFilter();

    private SequentViewLogicPrinter printer;
    private Proof proof;
    private Node selectedNode;
    private String printed;
    private Range highlightedRange;

    // search state (Swing SequentViewSearchBar)
    /** the matches of the current query as {@code [start, end)} ranges into {@link #printed}. */
    private final List<int[]> searchMatches = new ArrayList<>();
    /** the index of the current match in {@link #searchMatches}, {@code -1} if none. */
    private int searchResultPos = -1;

    private KeYSelectionModel selectionModel;
    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedNodeChanged(KeYSelectionEvent<Node> event) {
            display(selectionModel.getSelectedNode());
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            // setSelectedProof fires only the proof event (no node event); re-display here,
            // mirroring MainWindow.setSequentView of the Swing UI
            display(selectionModel.getSelectedNode());
        }
    };

    private Consumer<PosInSequent> onPosSelected = pos -> {
    };

    /**
     * Creates an empty sequent view.
     */
    public SequentViewF() {
        getStyleClass().add("sequent-view");
        scrollPane.getStyleClass().add("sequent-view");
        scrollPane.setFitToWidth(true);
        scrollPane.setFitToHeight(true);
        scrollPane.setContent(textFlow);
        setCenter(scrollPane);
        textFlow.getStyleClass().add("sequent-view-flow");
        textFlow.setPadding(new Insets(6));
        textFlow.setOnMouseClicked(this::handleMouseClick);
        printPlaceholder();

        createSearchBar();
        setBottom(searchBar);
        searchBar.setVisible(false);
        searchBar.setManaged(false);
        // Swing SequentView registers Ctrl+Shift+F with WHEN_ANCESTOR_OF_FOCUSED_COMPONENT: the
        // shortcut fires whenever the keyboard focus is anywhere inside this view (the key
        // events bubble from the focused control up to this pane).
        setOnKeyPressed(this::handlePaneKeyPressed);
    }

    /**
     * Builds the search bar (Swing {@code SearchBar}): a labeled text field, the RegExp toggle,
     * prev/next/close buttons. Live search on every keystroke, {@code Enter} selects the next
     * match, {@code Escape} closes the bar.
     */
    private void createSearchBar() {
        searchBar.getStyleClass().add("sequent-search-bar");
        searchBar.setPadding(new Insets(4));

        Button prevButton = new Button();
        prevButton.setGraphic(IconFactoryF.createIcon(IconFactoryF.Key.PREVIOUS));
        prevButton.getStyleClass().add("sequent-search-button");
        prevButton.setTooltip(new Tooltip("Previous match"));
        prevButton.setOnAction(e -> searchPrevious());

        Button nextButton = new Button();
        nextButton.setGraphic(IconFactoryF.createIcon(IconFactoryF.Key.NEXT));
        nextButton.getStyleClass().add("sequent-search-button");
        nextButton.setTooltip(new Tooltip("Next match"));
        nextButton.setOnAction(e -> searchNext());

        Button closeButton = new Button();
        closeButton.setGraphic(IconFactoryF.createIcon(IconFactoryF.Key.CLOSE));
        closeButton.getStyleClass().add("sequent-search-button");
        closeButton.setTooltip(new Tooltip("Close search bar"));
        closeButton.setOnAction(e -> hideSearchBar());

        searchField.getStyleClass().add("sequent-search-field");
        searchField.setPromptText("Search sequent");
        HBox.setHgrow(searchField, Priority.ALWAYS);
        searchField.textProperty().addListener((obs, oldText, newText) -> runSearch());
        searchField.setOnAction(e -> searchNext());
        searchField.setOnKeyPressed(e -> {
            if (KeyCode.ESCAPE.equals(e.getCode())) {
                hideSearchBar();
            }
        });

        regexToggle.getStyleClass().add("sequent-search-regex");
        regexToggle.setSelected(false);
        regexToggle.setMinWidth(Region.USE_PREF_SIZE);
        regexToggle.setTooltip(new Tooltip("Evaluate as regular expression"));
        regexToggle.setOnAction(e -> {
            searchField.requestFocus();
            runSearch();
        });

        searchBar.getChildren().addAll(searchField, prevButton, nextButton, closeButton,
            regexToggle);
        searchBar.setOnKeyPressed(e -> {
            if (KeyCode.ESCAPE.equals(e.getCode())) {
                hideSearchBar();
            }
        });
    }

    private void handlePaneKeyPressed(KeyEvent event) {
        if (OPEN_SEARCH.match(event)) {
            event.consume();
            showSearchBar();
        }
    }

    /**
     * Registers this view as a selection listener on the given model and displays the currently
     * selected node, mirroring how the Swing {@code SequentView} observes the mediator's
     * selection model.
     *
     * @param model the selection model to observe
     */
    public void attach(KeYSelectionModel model) {
        Objects.requireNonNull(model);
        if (selectionModel == model) {
            return;
        }
        if (selectionModel != null) {
            selectionModel.removeKeYSelectionListener(selectionListener);
        }
        selectionModel = model;
        model.addKeYSelectionListenerChecked(selectionListener);
        display(model.getSelectedNode());
    }

    /**
     * Displays the sequent of the given node.
     *
     * @param node the node whose sequent is shown, may be {@code null} to reset the view
     */
    public void display(Node node) {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(() -> display(node));
            return;
        }
        highlightedRange = null;
        if (node == null) {
            proof = null;
            selectedNode = null;
            printer = null;
            printPlaceholder();
            return;
        }
        if (node.proof() != proof) {
            proof = node.proof();
            // TODO(M2c): share the NotationInfo and the term label visibility with the mediator
            printer = SequentViewLogicPrinter.positionPrinter(new NotationInfo(),
                node.proof().getServices(), NO_VISIBLE_TERM_LABELS);
        }
        selectedNode = node;
        printSequent();
    }

    /**
     * @return the displayed proof, or {@code null} if none is loaded
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * Re-prints the sequent of the currently selected node.
     */
    public void printSequent() {
        highlightedRange = null;
        if (printer == null || selectedNode == null) {
            printPlaceholder();
            return;
        }
        filter.setSequent(selectedNode.sequent());
        // TODO(M2): compute the line width from the font metrics and the viewport width
        printer.update(filter, PosTableLayouter.DEFAULT_LINE_WIDTH);
        printed = printer.result();
        rebuildRuns();
    }

    /**
     * @return the initial position table of the current printing, or {@code null}
     */
    public InitialPositionTable getInitialPositionTable() {
        return printer == null ? null : printer.layouter().getInitialPositionTable();
    }

    /**
     * Returns the text of the printed sequent covered by the given position; the JavaFX
     * counterpart of {@code SequentView.getHighlightedText(PosInSequent)}. Unlike the Swing
     * version, no offset correction is needed: the character indexes of the position table match
     * the printed string exactly (there is no HTML document shift).
     *
     * @param pos the position, may be {@code null}
     * @return the covered text, or the empty string
     */
    public String getHighlightedText(PosInSequent pos) {
        if (pos == null || printed == null || pos.getBounds() == null) {
            return "";
        }
        Range bounds = pos.getBounds();
        int start = Math.clamp(bounds.start(), 0, printed.length());
        int end = Math.clamp(bounds.start() + bounds.length(), start, printed.length());
        return printed.substring(start, end);
    }

    /**
     * Registers the handler invoked when the user clicks on a term.
     *
     * @param handler receives the position of the clicked term, or {@code null} when the click hit
     *        no position
     */
    public void setOnPosSelected(Consumer<PosInSequent> handler) {
        this.onPosSelected = handler == null ? pos -> {
        } : handler;
    }

    private void handleMouseClick(MouseEvent event) {
        InitialPositionTable table = getInitialPositionTable();
        if (table == null || printed == null) {
            return;
        }
        Point2D local = textFlow.sceneToLocal(event.getSceneX(), event.getSceneY());
        HitInfo hit = textFlow.getHitInfo(local);
        int charIndex = hit.getCharIndex();
        if (charIndex < 0 || charIndex >= printed.length()) {
            highlightedRange = null;
            rebuildRuns();
            onPosSelected.accept(null);
            return;
        }
        PosInSequent pos = table.getPosInSequent(charIndex, filter);
        Range bounds = pos != null ? pos.getBounds() : null;
        highlightedRange = bounds != null && bounds.length() > 0 ? bounds : null;
        rebuildRuns();
        onPosSelected.accept(pos);
    }

    // -----------------------------------------------------------------------
    // Search (Swing SequentViewSearchBar)
    // -----------------------------------------------------------------------

    /**
     * Shows the search bar (Swing: {@code Ctrl+Shift+F}) and focuses the field. A query kept
     * from a previous opening is re-applied.
     */
    public void showSearchBar() {
        searchBar.setVisible(true);
        searchBar.setManaged(true);
        searchField.selectAll();
        searchField.requestFocus();
        if (!searchField.getText().isEmpty()) {
            runSearch();
        }
    }

    /**
     * Hides the search bar and clears the highlights so the plain sequent is shown again (Swing
     * {@code setVisible(false)}). The field text is kept like in the Swing view and re-applied on
     * the next opening.
     */
    public void hideSearchBar() {
        searchBar.setVisible(false);
        searchBar.setManaged(false);
        if (!searchMatches.isEmpty() || searchResultPos >= 0) {
            searchMatches.clear();
            searchResultPos = -1;
            rebuildRuns();
        }
        setAlert(false);
        scrollPane.requestFocus();
    }

    /**
     * Runs the search for the current field text (Swing {@code search()}): highlights all
     * matches of the query in the rendered text. An invalid regular expression and a query
     * without matches switch the field to the alert styling.
     */
    private void runSearch() {
        String text = searchField.getText();
        searchMatches.clear();
        searchResultPos = -1;
        if (text.isEmpty()) {
            setAlert(false);
            rebuildRuns();
            return;
        }
        Pattern pattern;
        try {
            pattern = SearchSequentPrintFilter.createPattern(text, regexToggle.isSelected());
        } catch (IllegalRegexException e) {
            LOGGER.debug("runSearch: text={} invalid regex", text);
            setAlert(true);
            rebuildRuns();
            return;
        }
        if (pattern == null || printed == null) {
            setAlert(true);
            rebuildRuns();
            return;
        }
        // the Swing search matches against the text with non-breaking spaces normalized
        Matcher matcher = pattern.matcher(printed.replace('\u00A0', ' '));
        while (matcher.find()) {
            searchMatches.add(new int[] { matcher.start(), matcher.end() });
        }
        LOGGER.debug("runSearch: text={} matches={}", text, searchMatches.size());
        rebuildRuns();
        setAlert(searchMatches.isEmpty());
    }

    /** Switches to the next match (Swing {@code searchNext}), wrapping around. */
    public void searchNext() {
        if (searchMatches.isEmpty()) {
            return;
        }
        searchResultPos = (searchResultPos + 1) % searchMatches.size();
        rebuildRuns();
        scrollToMatch(searchResultPos);
    }

    /** Switches to the previous match (Swing {@code searchPrevious}), wrapping around. */
    public void searchPrevious() {
        if (searchMatches.isEmpty()) {
            return;
        }
        searchResultPos =
            (searchResultPos + searchMatches.size() - 1) % searchMatches.size();
        rebuildRuns();
        scrollToMatch(searchResultPos);
    }

    /**
     * Scrolls the current match into view (Swing {@code setCaretPosition(foundAt)}): the vertical
     * position of the match's shape is centered in the viewport.
     */
    private void scrollToMatch(int index) {
        int[] match = searchMatches.get(index);
        if (printed == null || match[0] >= printed.length()) {
            return;
        }
        textFlow.applyCss();
        textFlow.layout();
        double minY = Double.POSITIVE_INFINITY;
        for (PathElement element : textFlow.getRangeShape(match[0],
            Math.min(match[1], printed.length()), true)) {
            if (element instanceof MoveTo m) {
                minY = Math.min(minY, m.getY());
            } else if (element instanceof LineTo l) {
                minY = Math.min(minY, l.getY());
            } else if (element instanceof VLineTo v) {
                minY = Math.min(minY, v.getY());
            }
        }
        if (!Double.isFinite(minY)) {
            return;
        }
        double contentHeight = textFlow.getBoundsInLocal().getHeight();
        double viewHeight = scrollPane.getViewportBounds().getHeight();
        if (contentHeight <= viewHeight) {
            return;
        }
        double vvalue = (minY - viewHeight / 2.0) / (contentHeight - viewHeight);
        scrollPane.setVvalue(Math.clamp(vvalue, 0.0, 1.0));
    }

    private void setAlert(boolean alert) {
        if (alert) {
            searchField.getStyleClass().add("search-alert");
        } else {
            searchField.getStyleClass().remove("search-alert");
        }
    }

    // -----------------------------------------------------------------------

    private void rebuildRuns() {
        textFlow.getChildren().clear();
        if (printed == null || printed.isEmpty()) {
            return;
        }
        Font font = ConfigF.DEFAULT.monoFont();

        // highlight intervals: the clicked term plus the search matches; the current search
        // match is styled stronger (Swing highlight_1 vs highlight_2)
        List<int[]> intervals = new ArrayList<>();
        List<String> intervalStyles = new ArrayList<>();
        if (highlightedRange != null) {
            int start = Math.clamp(highlightedRange.start(), 0, printed.length());
            int end = Math.clamp(highlightedRange.start() + highlightedRange.length(), start,
                printed.length());
            if (end > start) {
                intervals.add(new int[] { start, end });
                intervalStyles.add("sequent-term-highlight");
            }
        }
        for (int i = 0; i < searchMatches.size(); i++) {
            intervals.add(searchMatches.get(i));
            intervalStyles.add(i == searchResultPos ? "sequent-search-match-current"
                    : "sequent-search-match");
        }
        if (intervals.isEmpty()) {
            addRun(printed, font, "sequent-text");
            return;
        }

        // split the text at every interval boundary and style each segment with the classes of
        // all intervals covering it
        TreeSet<Integer> points = new TreeSet<>();
        points.add(0);
        points.add(printed.length());
        for (int[] interval : intervals) {
            if (interval[0] > 0 && interval[0] < printed.length()) {
                points.add(interval[0]);
            }
            if (interval[1] > 0 && interval[1] < printed.length()) {
                points.add(interval[1]);
            }
        }
        Integer[] sorted = points.toArray(new Integer[0]);
        for (int p = 0; p < sorted.length - 1; p++) {
            int start = sorted[p];
            int end = sorted[p + 1];
            List<String> styles = new ArrayList<>();
            styles.add("sequent-text");
            for (int i = 0; i < intervals.size(); i++) {
                int[] interval = intervals.get(i);
                if (interval[0] <= start && end <= interval[1]) {
                    styles.add(intervalStyles.get(i));
                }
            }
            addRun(printed.substring(start, end), font, styles.toArray(new String[0]));
        }
    }

    private void addRun(String content, Font font, String... styleClasses) {
        if (content.isEmpty()) {
            return;
        }
        Text run = new Text(content);
        run.getStyleClass().addAll(styleClasses);
        run.setFont(font);
        textFlow.getChildren().add(run);
    }

    private void printPlaceholder() {
        textFlow.getChildren().clear();
        Text placeholder = new Text("No proof loaded.\n"
            + "Start with -Dkey.fx.demo.sequent=<file.key> to try the sequent view spike.");
        placeholder.getStyleClass().add("sequent-placeholder");
        placeholder.setFont(ConfigF.DEFAULT.systemFont());
        textFlow.getChildren().add(placeholder);
    }

    /**
     * For tests: the current selection highlight range.
     */
    Range highlightedRange() {
        return highlightedRange;
    }

    /**
     * For tests: the printed sequent string.
     */
    String printed() {
        return printed;
    }

    /**
     * Development self-test (M2): exercises the sequent search bar like the Swing one — searches
     * the given term, checks that the matches are valid ranges into the printed text, navigates
     * with next and restores the plain view.
     *
     * @param query the query to search for
     * @return a one-line report, {@code "... PASS"} if the search behaves as expected
     */
    public String verifySequentSearch(String query) {
        if (printed == null) {
            return "no printed sequent";
        }
        showSearchBar();
        searchField.setText(query);
        int count = searchMatches.size();
        boolean rangesOk = true;
        for (int[] match : searchMatches) {
            rangesOk &= match[0] >= 0 && match[1] > match[0] && match[1] <= printed.length();
        }
        // the current match starts at -1 (none highlighted); next/prev cycle through the matches
        searchNext();
        int first = searchResultPos;
        searchNext();
        int second = searchResultPos;
        searchPrevious();
        int back = searchResultPos;
        searchPrevious();
        int wrapped = searchResultPos;
        hideSearchBar();
        boolean pass = count > 0 && rangesOk && first == 0 && second == 1 && back == 0
                && wrapped == count - 1 && searchMatches.isEmpty();
        return "query=" + query + " matches=" + count + " next=" + first + "," + second + ","
            + back + "," + wrapped + " rangesOk=" + rangesOk + " " + (pass ? "PASS" : "FAIL");
    }

    /**
     * Development self-test (M2a): verifies that the character model of the {@link TextFlow}
     * matches the {@link InitialPositionTable}. Every non-whitespace character of the printed
     * sequent is round-tripped: the on-screen bounds of the character are computed via
     * {@link TextFlow#getRangeShape(int, int, boolean)}, the center of the resulting shape is
     * mapped back through {@link TextFlow#getHitInfo} to a character index, and the
     * {@link PosInSequent} of both indexes must agree. This is the same mapping the mouse-click
     * handler performs.
     *
     * @return a one-line report, {@code "... PASS"} if the mapping is consistent
     */
    public String verifyPositionMapping() {
        if (printed == null || textFlow.getChildren().isEmpty()) {
            return "no printed sequent";
        }
        // make sure the text flow is laid out before asking for glyph shapes
        textFlow.applyCss();
        textFlow.layout();

        InitialPositionTable table = getInitialPositionTable();
        if (table == null) {
            return "no position table";
        }
        int chars = printed.length();
        int sampled = 0;
        int exact = 0;
        int tolerant = 0;
        int mismatches = 0;
        int firstMismatch = -1;
        for (int i = 0; i < chars; i++) {
            char c = printed.charAt(i);
            if (Character.isWhitespace(c)) {
                continue;
            }
            sampled++;
            HitInfo hit = textFlow.getHitInfo(centerOfRangeShape(i));
            if (hit == null) {
                mismatches++;
                if (firstMismatch < 0) {
                    firstMismatch = i;
                }
                continue;
            }
            int j = hit.getCharIndex();
            if (j == i) {
                exact++;
                continue;
            }
            PosInSequent posI = table.getPosInSequent(i, filter);
            PosInSequent posJ = table.getPosInSequent(j, filter);
            if (Math.abs(j - i) <= 1 && Objects.equals(posI, posJ)) {
                tolerant++;
            } else {
                mismatches++;
                if (firstMismatch < 0) {
                    firstMismatch = i;
                }
            }
        }
        String result = mismatches == 0 ? "PASS" : "FAIL";
        return "chars=" + chars + " sampled=" + sampled + " exact=" + exact + " tolerant="
            + tolerant + " mismatches=" + mismatches
            + (firstMismatch >= 0 ? " firstMismatch=" + firstMismatch : "") + " " + result;
    }

    /**
     * @return the center of the on-screen shape of the character at {@code index} in the local
     *         coordinates of the text flow
     */
    private Point2D centerOfRangeShape(int index) {
        PathElement[] elements = textFlow.getRangeShape(index, index + 1, true);
        double minX = Double.POSITIVE_INFINITY;
        double minY = Double.POSITIVE_INFINITY;
        double maxX = Double.NEGATIVE_INFINITY;
        double maxY = Double.NEGATIVE_INFINITY;
        for (PathElement element : elements) {
            double x = Double.NaN;
            double y = Double.NaN;
            if (element instanceof MoveTo m) {
                x = m.getX();
                y = m.getY();
            } else if (element instanceof LineTo l) {
                x = l.getX();
                y = l.getY();
            } else if (element instanceof HLineTo h) {
                x = h.getX();
            } else if (element instanceof VLineTo v) {
                y = v.getY();
            }
            if (!Double.isNaN(x)) {
                minX = Math.min(minX, x);
                maxX = Math.max(maxX, x);
            }
            if (!Double.isNaN(y)) {
                minY = Math.min(minY, y);
                maxY = Math.max(maxY, y);
            }
        }
        return new Point2D((minX + maxX) / 2.0, (minY + maxY) / 2.0);
    }
}
