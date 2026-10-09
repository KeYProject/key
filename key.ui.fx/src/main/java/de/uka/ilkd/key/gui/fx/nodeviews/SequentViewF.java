/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.TreeSet;
import java.util.function.Consumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javafx.animation.PauseTransition;
import javafx.geometry.Insets;
import javafx.geometry.Point2D;
import javafx.scene.control.Button;
import javafx.scene.control.ComboBox;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.CustomMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.MenuItem;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleButton;
import javafx.scene.control.Tooltip;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import javafx.scene.input.MouseButton;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.StackPane;
import javafx.scene.shape.HLineTo;
import javafx.scene.shape.LineTo;
import javafx.scene.shape.MoveTo;
import javafx.scene.shape.Path;
import javafx.scene.shape.PathElement;
import javafx.scene.shape.VLineTo;
import javafx.scene.text.Font;
import javafx.scene.text.HitInfo;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;
import javafx.util.Duration;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.pp.HideSequentPrintFilter;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.IllegalRegexException;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.RegroupSequentPrintFilter;
import de.uka.ilkd.key.pp.SearchSequentPrintFilter;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentPrintFilterEntry;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.Nullable;
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
 * {@code Ctrl+Shift+F}, close with {@code Escape}. The mode combo ports the Swing modes: Highlight
 * keeps the sequent unchanged; Hide only prints the formulas matching the query
 * ({@code HideSequentPrintFilter}); Regroup arranges the matching formulas around the sequent
 * arrow ({@code RegroupSequentPrintFilter}) — both filters are reused from {@code key.core} and
 * drive the printer like in Swing, so the click→position mapping follows the filtered printing.
 * While a search filter hides formulas, a warning banner shows the Swing
 * {@code SequentHideWarningBorder} message.
 * <p>
 * <b>Update highlights</b> (Swing {@code CurrentGoalView.updateUpdateHighlights}): the ranges of
 * the printed update operators, reported by {@link InitialPositionTable#getUpdateRanges()}, are
 * painted as translucent rectangles behind the text ({@link TextFlow#getRangeShape} shapes in an
 * overlay pane; Swing paints the same ranges with the HTML +1 offset that the FX view does not
 * need). The term under the mouse gets the same treatment as the Swing hover highlight
 * ({@code DEFAULT_HIGHLIGHT_COLOR}).
 * <p>
 * <b>Tooltip</b> (Swing {@code SequentView.getToolTipText}): hovering a position shows the
 * operator class, operator and sort of the term at that position in a {@link Tooltip} shown after
 * a short delay; gated by the shared {@code ViewSettings.isShowSequentViewTooltips()} like in
 * Swing.
 * <p>
 * Deliberately deferred to later chunks: mediator wiring (shared {@code NotationInfo} and term
 * label visibility), the tooltip strings of the GUI extensions ({@code KeYGuiExtensionFacade}
 * has no FX counterpart yet), and the search-mode menu items of the Swing proof-tree popup
 * ({@code SearchModeChangeAction}, M3 popups).
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

    // lemmaorigin: begin — term-label visibility hook (Swing SequentView.getVisibleTermLabels,
    // which feeds mainWindow.getVisibleTermLabels() to the printer). Defaults to the spike stub
    // so the view is unchanged until de.uka.ilkd.key.gui.fx.originlabels.TermLabelMenuF attaches.
    private VisibleTermLabels visibleTermLabels = NO_VISIBLE_TERM_LABELS;

    /**
     * Installs the given visible-term-labels provider and re-creates the printer with it (Swing
     * {@code SequentView} passes {@code mainWindow.getVisibleTermLabels()} to every printer). The
     * printer must be rebuilt because the label visibility is bound at construction; a plain
     * {@link #printSequent()} suffices for later visibility changes, since the manager is
     * consulted live while printing.
     *
     * @param labels the label visibility to use from now on, {@code null} restores the stub
     */
    public void setVisibleTermLabels(VisibleTermLabels labels) {
        visibleTermLabels = labels != null ? labels : NO_VISIBLE_TERM_LABELS;
        if (printer != null && selectedNode != null) {
            printer = SequentViewLogicPrinter.positionPrinter(new NotationInfo(),
                selectedNode.proof().getServices(), visibleTermLabels);
            if (filter instanceof SearchSequentPrintFilter searchFilter) {
                searchFilter.setLogicPrinter(printer);
            }
            printSequent();
        }
    }

    /**
     * The printed sequent string of the current display, for the term-label self test
     * ({@code key.fx.verify.lemmaorigin}).
     */
    public String printedText() {
        return printed;
    }

    // lemmaorigin: end

    private static final KeyCombination OPEN_SEARCH =
        new KeyCodeCombination(KeyCode.F, KeyCombination.CONTROL_DOWN, KeyCombination.SHIFT_DOWN);

    private final ScrollPane scrollPane = new ScrollPane();
    private final TextFlow textFlow = new TextFlow();
    /**
     * Translucent rectangles painted behind the printed text (Swing's highlighter layer): the
     * update-operator highlight of the current printing. The pane fills the same area as the
     * {@link #textFlow} inside the content {@link StackPane}, so the {@link TextFlow} local
     * coordinates of {@link TextFlow#getRangeShape} address it directly.
     */
    private final Pane updateOverlay = new Pane();
    /**
     * Overlay pane for the term under the mouse (Swing {@code DEFAULT_HIGHLIGHT_COLOR} hover
     * highlight), above the update highlights, behind the text.
     */
    private final Pane hoverOverlay = new Pane();

    private final HBox searchBar = new HBox(4);
    private final TextField searchField = new TextField();
    private final ToggleButton regexToggle = new ToggleButton("RegExp");
    /** the search mode combo (Swing {@code SequentViewSearchBar.searchModeBox}). */
    private final ComboBox<SearchMode> searchModeBox = new ComboBox<>();

    /**
     * the warning banner shown while a search filter hides formulas (Swing
     * {@code SequentHideWarningBorder} message).
     */
    private final Label hideWarning = new Label(WARNING_TEXT);

    /**
     * The current sequent print filter (Swing {@code SequentView.filter}): the identity filter by
     * default; the search bar's Hide/Regroup modes install the print filters of {@code key.core}.
     */
    private SequentPrintFilter filter = new IdentitySequentPrintFilter();

    private SequentViewLogicPrinter printer;
    private Proof proof;
    private Node selectedNode;
    private String printed;
    private Range highlightedRange;

    /** Syntax highlighting on/off (Swing View menu, on by default). */
    private boolean syntaxHighlighting = true;

    /** The syntax highlight intervals of the current printing, sorted by start. */
    private List<SequentSyntaxHighlighterF.Highlight> syntaxHighlights = List.of();

    // search state (Swing SequentViewSearchBar)
    /** the matches of the current query as {@code [start, end)} ranges into {@link #printed}. */
    private final List<int[]> searchMatches = new ArrayList<>();
    /** the index of the current match in {@link #searchMatches}, {@code -1} if none. */
    private int searchResultPos = -1;

    // update highlights (Swing CurrentGoalView.updateUpdateHighlights)
    /** number of update-highlight rectangles currently displayed. */
    private int updateRectCount;

    // hover highlight + tooltip (Swing SequentViewInputListener.mouseMoved / getToolTipText)
    /** the term range under the mouse, {@code null} when the mouse is over empty space. */
    private Range hoveredRange;
    /** shows the term info of the hovered position after the Swing-like display delay. */
    private final Tooltip hoverTooltip = new Tooltip();
    /** delay before the tooltip shows (Swing ToolTipManager initial delay ≈ 500 ms). */
    private final PauseTransition hoverTooltipDelay =
        new PauseTransition(Duration.millis(600));
    /** last mouse screen position for placing the tooltip below-right of the cursor. */
    private double hoverScreenX;
    private double hoverScreenY;

    /** the warning message painted by the Swing {@code SequentHideWarningBorder}. */
    private static final String WARNING_TEXT = "Some formulas have been hidden (by search phrase)";

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
        // the overlay panes fill the same area as the text flow, so the TextFlow local
        // coordinates of the range shapes can be used directly; they sit behind the text like
        // the Swing highlighter layer and never receive mouse events
        updateOverlay.getStyleClass().add("sequent-overlay");
        updateOverlay.setMouseTransparent(true);
        updateOverlay.setMaxSize(Double.MAX_VALUE, Double.MAX_VALUE);
        hoverOverlay.getStyleClass().add("sequent-overlay");
        hoverOverlay.setMouseTransparent(true);
        hoverOverlay.setMaxSize(Double.MAX_VALUE, Double.MAX_VALUE);
        StackPane content = new StackPane(updateOverlay, hoverOverlay, textFlow);
        scrollPane.setContent(content);
        setCenter(scrollPane);
        textFlow.getStyleClass().add("sequent-view-flow");
        textFlow.setPadding(new Insets(6));
        textFlow.setOnMouseClicked(this::handleMouseClick);
        textFlow.setOnMouseMoved(this::handleMouseMove);
        textFlow.setOnMouseExited(this::handleMouseExited);
        // recompute the overlay rectangles when the layout changes (viewport resize); the prints
        // rebuild them directly
        textFlow.layoutBoundsProperty()
                .addListener((obs, oldBounds, newBounds) -> FxUtil.runLater(this::rebuildOverlays));
        // the tooltip shows when the mouse pauses over a term (Swing ToolTipManager)
        hoverTooltipDelay.setOnFinished(event -> showHoverTooltip());

        // the warning banner replaces the Swing SequentHideWarningBorder painted around the
        // enclosing panel; hidden (and unmanaged) unless a search filter hides formulas
        hideWarning.getStyleClass().add("sequent-hide-warning");
        hideWarning.setManaged(false);
        hideWarning.setVisible(false);
        setTop(hideWarning);

        createSearchBar();
        setBottom(searchBar);
        searchBar.setVisible(false);
        searchBar.setManaged(false);
        // Swing SequentView registers Ctrl+Shift+F with WHEN_ANCESTOR_OF_FOCUSED_COMPONENT: the
        // shortcut fires whenever the keyboard focus is anywhere inside this view (the key
        // events bubble from the focused control up to this pane).
        setOnKeyPressed(this::handlePaneKeyPressed);
        printPlaceholder();
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

        searchModeBox.getStyleClass().add("sequent-search-mode");
        searchModeBox.setMaxWidth(Region.USE_PREF_SIZE);
        searchModeBox.getItems().addAll(SearchMode.values());
        searchModeBox.setCellFactory(view -> new SearchModeListCell());
        searchModeBox.setButtonCell(new SearchModeListCell());
        searchModeBox.setTooltip(new Tooltip("Determines search behaviour: Hide only shows "
            + "sequent formulas that match the search. Regroup arranges the matching formulas "
            + "around the sequent arrow. Highlight leaves the sequent unchanged."));
        searchModeBox.getSelectionModel().select(SearchMode.HIGHLIGHT);
        searchModeBox.setOnAction(e -> applySearchMode(searchModeBox.getValue()));

        searchBar.getChildren().addAll(searchField, prevButton, nextButton, closeButton,
            regexToggle, searchModeBox);
        searchBar.setOnKeyPressed(e -> {
            if (KeyCode.ESCAPE.equals(e.getCode())) {
                hideSearchBar();
            }
        });
    }

    /**
     * A combo cell with the mode name and icon (Swing {@code SearchMode} items carry icons).
     */
    private static final class SearchModeListCell extends ListCell<SearchMode> {
        @Override
        protected void updateItem(SearchMode item, boolean empty) {
            super.updateItem(item, empty);
            if (empty || item == null) {
                setText(null);
                setGraphic(null);
            } else {
                setText(item.getDisplayName());
                setGraphic(IconFactoryF.createIcon(item.getIcon()));
            }
        }
    }

    /**
     * The search modes of the sequent search bar (Swing
     * {@code SequentViewSearchBar.SearchMode}): Highlight leaves the sequent unchanged, Hide only
     * shows the formulas matching the query and Regroup arranges the matching formulas around the
     * sequent arrow. Hide and Regroup are print filters reused from {@code key.core}.
     */
    public enum SearchMode {
        HIGHLIGHT("Highlight", IconFactoryF.Key.SEARCH_HIGHLIGHT),
        HIDE("Hide", IconFactoryF.Key.SEARCH_HIDE),
        REGROUP("Regroup", IconFactoryF.Key.SEARCH_REGROUP);

        private final String displayName;
        private final IconFactoryF.Key icon;

        SearchMode(String name, IconFactoryF.Key icon) {
            this.displayName = name;
            this.icon = icon;
        }

        public String getDisplayName() {
            return displayName;
        }

        public IconFactoryF.Key getIcon() {
            return icon;
        }

        @Override
        public String toString() {
            return displayName;
        }
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
            // lemmaorigin: use the installed label visibility (Swing SequentView printer setup)
            printer = SequentViewLogicPrinter.positionPrinter(new NotationInfo(),
                node.proof().getServices(), visibleTermLabels);
            if (filter instanceof SearchSequentPrintFilter searchFilter) {
                // the search filters print single formulas through the view's printer (Swing
                // SequentViewSearchBar.search refreshes it the same way)
                searchFilter.setLogicPrinter(printer);
            }
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
     * menu: MP3a — re-creates the printer with a {@link NotationInfo} refreshed from the current
     * view settings, so the View-menu Pretty Print / Unicode Symbols toggles change the printed
     * symbols (Swing {@code MainWindow.makePrettyView}, MainWindow.java:954-959: refresh the
     * mediator's shared NotationInfo against the services and re-display the sequent
     * {@code SwingUtilities.invokeLater(this::updateSequentView)}). The FX sequent view builds
     * its own {@code NotationInfo} per proof ({@link #display(Node)} — it does not use the
     * mediator's shared instance yet), so this mirrors the printer rebuild of
     * {@link #setVisibleTermLabels(VisibleTermLabels)} with the settings passed to
     * {@code NotationInfo.refresh(Services, boolean, boolean, boolean)}
     * (NotationInfo.java:425-438): {@code (isUsePretty(), isUseUnicode(), isHidePackagePrefix())}
     * exactly like Swing's {@code ViewSettings}-driven refresh, keeping the search filter re-bound
     * to the new printer and re-printing the current node.
     */
    public void refreshPrettyView() {
        if (printer == null || selectedNode == null) {
            return;
        }
        ViewSettings viewSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        NotationInfo notationInfo = new NotationInfo();
        notationInfo.refresh(selectedNode.proof().getServices(), viewSettings.isUsePretty(),
            viewSettings.isUseUnicode(), viewSettings.isHidePackagePrefix());
        printer = SequentViewLogicPrinter.positionPrinter(notationInfo,
            selectedNode.proof().getServices(), visibleTermLabels);
        if (filter instanceof SearchSequentPrintFilter searchFilter) {
            // the search filters print single formulas through the view's printer (Swing
            // SequentViewSearchBar.search refreshes it the same way)
            searchFilter.setLogicPrinter(printer);
        }
        printSequent();
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
        LOGGER.debug("printSequent: chars={} filter={} antec={} succ={}", printed.length(), filter
                .getClass().getSimpleName(),
            filter.getFilteredAntec() == null ? -1 : filter.getFilteredAntec().size(),
            filter.getFilteredSucc() == null ? -1 : filter.getFilteredSucc().size());
        syntaxHighlights = syntaxHighlighting
                ? SequentSyntaxHighlighterF.highlight(printed, selectedNode)
                : List.of();
        syntaxHighlights.sort((a, b) -> Integer.compare(a.start(), b.start()));
        // the reprint invalidates the mouse-dependent state (Swing's setText clears the
        // highlights, CurrentGoalView re-paints the update highlights afterwards)
        clearHover();
        rebuildRuns();
        updateHideWarning();
        rebuildOverlays();
    }

    /**
     * Switches the syntax highlighting of the printed sequent (Swing View menu "Syntax
     * Highlighting").
     *
     * @param enabled {@code true} to color keywords, program variables and comments
     */
    public void setSyntaxHighlightingEnabled(boolean enabled) {
        if (syntaxHighlighting == enabled) {
            return;
        }
        syntaxHighlighting = enabled;
        printSequent();
    }

    /**
     * @return whether the syntax highlighting of the printed sequent is enabled
     */
    public boolean isSyntaxHighlightingEnabled() {
        return syntaxHighlighting;
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
        // termmenu: a right-click shows the sequent context menu instead of running the
        // selection path below (Swing CurrentGoalViewListener: a right mouse click builds
        // CurrentGoalViewMenu at the caret position and shows it at the mouse location); the
        // left-click selection / highlight logic is left untouched
        if (event.getButton() == MouseButton.SECONDARY) {
            showContextMenu(event);
            return;
        }
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
        lastClickedPos = pos; // lemmaorigin: remember the clicked term (Swing context-menu target)
        Range bounds = pos != null ? pos.getBounds() : null;
        highlightedRange = bounds != null && bounds.length() > 0 ? bounds : null;
        rebuildRuns();
        onPosSelected.accept(pos);
    }

    // termmenu: begin — right-click sequent context menu (SequentMenuModelF +
    // SequentTermContextMenuF)
    /**
     * Builds and shows the sequent context menu at the given right-click position (Swing
     * {@code CurrentGoalViewListener.mouseClicked}: the menu is built from the
     * {@link PosInSequent} at the caret position and displayed at the mouse location). A no-op
     * until the menu context ({@link #setMenuContext}) and a printable position are available.
     *
     * @param event the right-click event
     */
    private void showContextMenu(MouseEvent event) {
        if (menuMediator == null || menuProofControl == null) {
            return;
        }
        Goal goal = menuMediator.getSelectedGoal();
        if (goal == null) {
            return;
        }
        PosInSequent pos = getSequentPosAt(charIndexOf(event));
        if (pos == null) {
            return;
        }
        List<SequentMenuModelF.Entry> entries =
            SequentMenuModelF.build(pos, menuMediator, menuProofControl, null, null);
        ContextMenu fallback = SequentTermContextMenuF.build(entries,
            new SequentTermContextMenuF.MenuContext(menuMediator, menuProofControl, goal, pos,
                null, this::printSequent));
        // menu: MP7 — the macro popup replaces the term menu while "Right Click for Proof Macros"
        // is active ({@link #buildRightClickMenu} falls back to the term menu when no macro is
        // applicable)
        ContextMenu menu = buildRightClickMenu(pos, fallback);
        menu.show(textFlow, event.getScreenX(), event.getScreenY());
    }

    // menu: MP7 — begin — right-click proof-macro popup (Swing CurrentGoalViewListener.java:54-67
    // + ProofMacroMenu)
    /**
     * menu: MP7 — the right-click popup seam: with the "Right Click for Proof Macros" setting
     * active the macro popup replaces the term context menu (Swing
     * {@code CurrentGoalViewListener.mouseClicked}, CurrentGoalViewListener.java:53-67: {@code
     * isRightClickMacro()} selects {@code ProofMacroMenu} over the taclet menu); when no macro is
     * applicable the term menu is used (Swing politely adds a "No strategies available" label,
     * CurrentGoalViewListener.java:62-64 / {@code ProofMacroMenu.isEmpty()}, ProofMacroMenu.java
     * :160-162 — the term menu is the FX equivalent fallback).
     *
     * @param pos the clicked sequent position (already non-null for the interactive callers)
     * @param fallback the term context menu built for the same position
     * @return the popup to show
     */
    private ContextMenu buildRightClickMenu(PosInSequent pos, ContextMenu fallback) {
        if (ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isRightClickMacro()) {
            ContextMenu macroMenu = buildMacroPopup(pos);
            if (macroMenu != null) {
                return macroMenu;
            }
        }
        return fallback;
    }

    /**
     * menu: MP7 — builds the macro popup for the clicked position: one item per macro of the
     * Automation submenu's {@link MainWindowF#AUTOMATION_MACROS} list that is applicable at the
     * position (Swing {@code ProofMacroMenu} iterates the registered macros and keeps those with
     * {@code canApplyTo}, ProofMacroMenu.java:87-99); item text = {@code macro.getName()}, tooltip
     * = {@code macro.getDescription()} (ProofMacroMenu.java:143-144). The action runs the macro on
     * the selected node with the {@link PosInOccurrence} of the clicked position (Swing
     * {@code ProofMacroUserAction}, ProofMacroUserAction.java:57-59: {@code
     * mediator.getUI().getProofControl().runMacro(node, macro, pio)}; the core silently ignores
     * the run while auto mode is active, and the {@code pio} may be {@code null} — the position
     * may resolve to no occurrence and global macros accept that). Returns {@code null} when no
     * macro is applicable (the caller then falls back to the term menu).
     *
     * @param pos the clicked sequent position or {@code null}
     * @return the macro popup, or {@code null} if no macro is applicable
     */
    private ContextMenu buildMacroPopup(@Nullable PosInSequent pos) {
        Node node = menuMediator.getSelectedNode();
        Goal goal = menuMediator.getSelectedGoal();
        if (node == null || goal == null) {
            return null;
        }
        Proof proof = node.proof();
        PosInOccurrence pio = pos == null ? null : pos.getPosInOccurrence();
        ImmutableList<Goal> goals = proof.getSubtreeEnabledGoals(node);
        ContextMenu menu = new ContextMenu();
        int count = 0;
        for (ProofMacro macro : MainWindowF.AUTOMATION_MACROS) {
            if (macro.canApplyTo(proof, goals, pio)) {
                // menu: MP7/MP8 — the item construction (name label + description tooltip via
                // CustomMenuItem, since JavaFX MenuItem has no tooltip property) is shared with
                // the term-menu "Strategy Macros" section, see {@link ProofMacroMenuF#itemFor}.
                menu.getItems().add(ProofMacroMenuF.itemFor(macro, node, menuProofControl, pio));
                count++;
            }
        }
        return count == 0 ? null : menu;
    }

    /**
     * menu: MP7 — the visible text of a menu item: the item text, or the content text of a
     * {@link CustomMenuItem} (the macro popup uses label-backed custom items for the tooltips),
     * or the empty string. {@code getText()} may be {@code null} (e.g. separators/Swing-ish
     * placeholder items of the term menu), which counts as empty.
     */
    private static String visibleText(MenuItem item) {
        String text = item.getText();
        if (text != null && !text.isEmpty()) {
            return text;
        }
        if (item instanceof CustomMenuItem custom && custom.getContent() instanceof Label label) {
            return label.getText();
        }
        return "";
    }

    /**
     * menu: MP7 — the labels of the given menu items (separators skipped, sub-menus flattened).
     */
    private static List<String> menuLabels(List<MenuItem> items) {
        List<String> labels = new ArrayList<>();
        for (MenuItem item : items) {
            if (!(item instanceof javafx.scene.control.SeparatorMenuItem)) {
                String text = visibleText(item);
                if (!text.isEmpty()) {
                    labels.add(text);
                }
            }
            if (item instanceof javafx.scene.control.Menu subMenu) {
                labels.addAll(menuLabels(subMenu.getItems()));
            }
        }
        return labels;
    }

    /**
     * menu: MP7 — headless self test of the right-click popup ({@code
     * key.fx.verify.rightclickmacro}), run after the demo load from MainWindowF: computes a
     * {@link PosInSequent} of the current printing and builds the popup through the
     * {@link #buildRightClickMenu} seam with the "Right Click for Proof Macros" flag ON and OFF
     * (the persisted setting is restored afterwards). With the flag ON the popup must contain the
     * macro names of the Automation submenu ({@link MainWindowF#AUTOMATION_MACROS}) and no
     * term-menu entries; with the flag OFF the term-menu path must be taken. Uses the printed
     * position table — no synthetic mouse events. Skips gracefully without a goal or position.
     *
     * @return {@code "PASS - ..."} or {@code "FAIL - ..."}
     */
    public String verifyRightClickMacro() {
        Goal goal = menuMediator == null ? null : menuMediator.getSelectedGoal();
        PosInSequent pos = firstIndexedPos();
        if (goal == null || pos == null) {
            return "SKIP - no goal/position (no printed sequent)";
        }
        List<SequentMenuModelF.Entry> entries =
            SequentMenuModelF.build(pos, menuMediator, menuProofControl, null, null);
        ContextMenu fallback = SequentTermContextMenuF.build(entries,
            new SequentTermContextMenuF.MenuContext(menuMediator, menuProofControl, goal, pos,
                null, this::printSequent));
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        boolean saved = gs.isRightClickMacro();
        try {
            gs.setRightClickMacros(true);
            ContextMenu on = buildRightClickMenu(pos, fallback);
            gs.setRightClickMacros(false);
            ContextMenu off = buildRightClickMenu(pos, fallback);
            List<String> onLabels = menuLabels(on.getItems());
            List<String> offLabels = menuLabels(off.getItems());
            List<String> macroNames = new ArrayList<>();
            for (ProofMacro macro : MainWindowF.AUTOMATION_MACROS) {
                macroNames.add(macro.getName());
            }
            boolean hasMacros = onLabels.containsAll(macroNames);
            // menu: MP8 — the macro popup must not contain any term-menu entry other than the
            // shared macro names: since MP8b the term menu has a "Strategy Macros" section with
            // the very same four macros, so the names are excluded from the comparison (the
            // MP7b term menu had them only in the macro popup).
            boolean noTermEntries = onLabels.stream()
                    .filter(l -> !macroNames.contains(l))
                    .noneMatch(offLabels::contains);
            // the OFF path is the term menu (fixed structural items of SequentTermContextMenuF)
            boolean termPath = offLabels.contains("Apply rules automatically here")
                    || offLabels.contains("Copy to clipboard")
                    || offLabels.contains("No rules applicable.");
            boolean pass = hasMacros && noTermEntries && termPath;
            return (pass ? "PASS" : "FAIL") + " - on[" + String.join(", ", onLabels) + "] off["
                + String.join(", ", offLabels) + "]";
        } finally {
            gs.setRightClickMacros(saved);
        }
    }

    /**
     * menu: MP7 — the first {@link PosInSequent} of the current printing (the printed text may
     * start with whitespace or symbols that do not map to a position — the first indexed
     * character that resolves is used).
     */
    private PosInSequent firstIndexedPos() {
        String text = printedText();
        if (text == null) {
            return null;
        }
        for (int i = 0; i < text.length(); i++) {
            PosInSequent pos = getSequentPosAt(i);
            if (pos != null) {
                return pos;
            }
        }
        return null;
    }
    // menu: MP7 — end

    /**
     * The character index of the printed text under the given mouse event (the same mapping
     * {@link #handleMouseClick} uses), or {@code -1} if the event does not address a character.
     */
    private int charIndexOf(MouseEvent event) {
        InitialPositionTable table = getInitialPositionTable();
        if (table == null || printed == null) {
            return -1;
        }
        Point2D local = textFlow.sceneToLocal(event.getSceneX(), event.getSceneY());
        HitInfo hit = textFlow.getHitInfo(local);
        int charIndex = hit == null ? -1 : hit.getCharIndex();
        return charIndex >= 0 && charIndex < printed.length() ? charIndex : -1;
    }
    // termmenu: end

    // lemmaorigin: begin — the last clicked position (Swing's term context-menu target; the
    // View▸Origin Tracking▸Show Origin item of OriginLabelsF uses it because the FX sequent view
    // has no context menu yet)
    private PosInSequent lastClickedPos;

    /**
     * @return the position of the last clicked term, or {@code null} if nothing was clicked or
     *         the click missed a position
     */
    public PosInSequent getLastClickedPos() {
        return lastClickedPos;
    }
    // lemmaorigin: end

    // termmenu: begin — right-click context menu support (S3 hit-test wiring): the shared
    // mediator + proof control supplied by MainWindowF (Swing parity: the sequent view builds
    // CurrentGoalViewMenu with the mediator's selected goal and the proof control of the loaded
    // environment) and the char-index → PosInSequent lookup shared by the right-click handler and
    // the key.fx.verify.termmenu self test.
    private KeYMediatorF menuMediator;
    private ProofControl menuProofControl;

    /**
     * Supplies the FX mediator and the proof control used to build the right-click sequent
     * context menu (Swing {@code MainWindow.setSequentView} passes its mediator and the proof
     * control of the loaded environment). No-op until both are set — the menu only appears when
     * the full context is available.
     *
     * @param mediator the shared mediator, {@code null} clears the reference
     * @param proofControl the proof control of the loaded environment, {@code null} clears it
     */
    public void setMenuContext(KeYMediatorF mediator, ProofControl proofControl) {
        this.menuMediator = mediator;
        this.menuProofControl = proofControl;
    }

    /**
     * @return the {@link PosInSequent} of the printed sequent at the given character index (the
     *         same lookup the mouse handlers perform), or {@code null} if there is no printing or
     *         the index does not address a position
     */
    public PosInSequent getSequentPosAt(int charIndex) {
        InitialPositionTable table = getInitialPositionTable();
        if (table == null || printed == null || charIndex < 0 || charIndex >= printed.length()) {
            return null;
        }
        return table.getPosInSequent(charIndex, filter);
    }
    // termmenu: end

    // -----------------------------------------------------------------------
    // Hover highlight + tooltip (Swing SequentViewInputListener.mouseMoved /
    // SequentView.getToolTipText)
    // -----------------------------------------------------------------------

    /**
     * Follows the mouse (Swing {@code mouseMoved}): the term under the cursor gets a translucent
     * highlight rectangle and the tooltip shows the term info of the hovered position.
     */
    private void handleMouseMove(MouseEvent event) {
        InitialPositionTable table = getInitialPositionTable();
        if (table == null || printed == null) {
            return;
        }
        Point2D local = textFlow.sceneToLocal(event.getSceneX(), event.getSceneY());
        HitInfo hit = textFlow.getHitInfo(local);
        int charIndex = hit == null ? -1 : hit.getCharIndex();
        PosInSequent pos =
            charIndex >= 0 && charIndex < printed.length() ? table.getPosInSequent(charIndex,
                filter) : null;
        Range bounds = pos != null ? pos.getBounds() : null;
        Range hover = bounds != null && bounds.length() > 0 ? bounds : null;
        if (!Objects.equals(hover, hoveredRange)) {
            hoveredRange = hover;
            rebuildHoverOverlay();
        }
        updateHoverTooltip(event, pos);
    }

    /**
     * Clears the hover state when the mouse leaves the view (Swing {@code mouseExited} →
     * {@code disableHighlights}).
     */
    private void handleMouseExited(MouseEvent event) {
        clearHover();
    }

    /** Clears the hovered term range and hides the tooltip. */
    private void clearHover() {
        if (hoveredRange != null) {
            hoveredRange = null;
            rebuildHoverOverlay();
        }
        hideHoverTooltip();
    }

    /** Stops the display delay and hides the tooltip (its content would be stale). */
    private void hideHoverTooltip() {
        hoverTooltipDelay.stop();
        if (hoverTooltip.isShowing()) {
            hoverTooltip.hide();
        }
    }

    /**
     * Shows the tooltip with the term info of the given position (Swing
     * {@code SequentView.getToolTipText}): operator class, operator and sort of the term. The
     * tooltip appears when the mouse pauses over a term; while it is visible its content updates
     * with the position.
     */
    private void updateHoverTooltip(MouseEvent event, PosInSequent pos) {
        hoverScreenX = event.getScreenX();
        hoverScreenY = event.getScreenY();
        String text = getTooltipText(pos);
        if (text.isEmpty()) {
            hideHoverTooltip();
            return;
        }
        hoverTooltip.setText(text);
        if (hoverTooltip.isShowing()) {
            // the content updates live while the mouse moves over terms
            return;
        }
        hoverTooltipDelay.playFromStart();
    }

    /** Shows the tooltip below-right of the current mouse position. */
    private void showHoverTooltip() {
        if (hoveredRange == null || hoverTooltip.getText() == null
                || hoverTooltip.getText().isEmpty()) {
            return;
        }
        var window = textFlow.getScene() != null ? textFlow.getScene().getWindow() : null;
        if (window == null || !window.isShowing()) {
            return;
        }
        if (!hoverTooltip.isShowing()) {
            hoverTooltip.show(textFlow, hoverScreenX + 16, hoverScreenY + 24);
        }
    }

    /**
     * The tooltip text for the given position (Swing {@code SequentView.getToolTipText} without
     * the HTML markup and without the GUI extension strings, which have no FX counterpart yet).
     * menu: MP3a — the {@code isShowSequentViewTooltips()} gate is driven by the View menu "Show
     * Tooltips in Sequent View" toggle (Swing {@code ToggleSequentViewTooltipAction}, NAME =
     * "Show Tooltips in Sequent View"); {@link #updateHoverTooltip} hides the tooltip whenever
     * this method returns the empty string, so no further gating is needed at the show site.
     */
    private String getTooltipText(PosInSequent pos) {
        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .isShowSequentViewTooltips()) {
            return "";
        }
        if (pos == null || pos.isSequent() || pos.getPosInOccurrence() == null) {
            return "";
        }
        Term term = pos.getPosInOccurrence().subTerm();
        return "Operator: " + term.op().getClass().getSimpleName() + " (" + term.op() + ")\nSort: "
            + term.sort();
    }

    // -----------------------------------------------------------------------
    // Overlay rectangles (Swing paints the same ranges with the highlighter behind the text)
    // -----------------------------------------------------------------------

    /** Rebuilds all overlay rectangles behind the text. */
    private void rebuildOverlays() {
        rebuildUpdateOverlays();
        rebuildHoverOverlay();
    }

    /**
     * Rebuilds the update-highlight rectangles of the current printing (Swing
     * {@code CurrentGoalView.updateUpdateHighlights}): one translucent rectangle per update range
     * of the position table, shaped with {@link TextFlow#getRangeShape}. Unlike the Swing view no
     * +1 offset is applied — the character indexes of the position table match the TextFlow
     * character model exactly.
     */
    private void rebuildUpdateOverlays() {
        updateOverlay.getChildren().clear();
        updateRectCount = 0;
        InitialPositionTable table = getInitialPositionTable();
        if (printed == null || table == null) {
            return;
        }
        // make sure the text flow is laid out before asking for glyph shapes
        textFlow.applyCss();
        textFlow.layout();
        for (Range range : table.getUpdateRanges()) {
            int start = Math.clamp(range.start(), 0, printed.length());
            int end = Math.clamp(range.end(), start, printed.length());
            if (end <= start) {
                continue;
            }
            updateOverlay.getChildren()
                    .add(rectForRange(start, end, "sequent-update-highlight"));
            updateRectCount++;
        }
    }

    /** Rebuilds the highlight rectangle of the term under the mouse. */
    private void rebuildHoverOverlay() {
        hoverOverlay.getChildren().clear();
        if (hoveredRange == null || printed == null) {
            return;
        }
        int start = Math.clamp(hoveredRange.start(), 0, printed.length());
        int end = Math.clamp(hoveredRange.start() + hoveredRange.length(), start,
            printed.length());
        if (end > start) {
            hoverOverlay.getChildren().add(rectForRange(start, end, "sequent-hover-highlight"));
        }
    }

    /**
     * @return a filled path over the on-screen shape of the given character range (a per-line
     *         polygon like the Swing highlighter paints)
     */
    private Path rectForRange(int start, int end, String styleClass) {
        Path rect = new Path(textFlow.getRangeShape(start, end, true));
        rect.getStyleClass().add(styleClass);
        rect.setManaged(false);
        return rect;
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
     * the next opening; the mode resets to Highlight, which reinstalls the identity filter.
     */
    public void hideSearchBar() {
        searchBar.setVisible(false);
        searchBar.setManaged(false);
        // Swing setVisible(false) resets the mode combo, which re-installs the identity filter
        if (searchModeBox.getValue() != SearchMode.HIGHLIGHT) {
            searchModeBox.getSelectionModel().select(SearchMode.HIGHLIGHT);
        }
        if (!searchMatches.isEmpty() || searchResultPos >= 0) {
            searchMatches.clear();
            searchResultPos = -1;
            rebuildRuns();
        }
        setAlert(false);
        scrollPane.requestFocus();
    }

    /**
     * Switches the sequent print filter to the given search mode (Swing
     * {@code SequentViewSearchBar}'s combo listener): Hide and Regroup install the print filters
     * of {@code key.core} on the view's printer, Highlight returns to the identity filter. The
     * search itself runs afterwards ({@link #runSearch()}, Swing {@code search()}).
     */
    private void applySearchMode(SearchMode mode) {
        if (mode == null) {
            return;
        }
        switch (mode) {
            case HIDE -> setSequentFilter(
                printer == null ? new IdentitySequentPrintFilter()
                        : new HideSequentPrintFilter(printer, regexToggle.isSelected()),
                false);
            case REGROUP -> setSequentFilter(
                printer == null ? new IdentitySequentPrintFilter()
                        : new RegroupSequentPrintFilter(printer, regexToggle.isSelected()),
                false);
            case HIGHLIGHT -> setSequentFilter(new IdentitySequentPrintFilter(), false);
        }
        LOGGER.debug("applySearchMode: {} filter={}", mode, filter.getClass().getSimpleName());
        runSearch();
    }

    /**
     * Sets the sequent print filter used for the next printing (Swing
     * {@code SequentView.setFilter}): the filter receives the selected sequent immediately, a
     * forced update re-prints.
     */
    private void setSequentFilter(SequentPrintFilter newFilter, boolean forceUpdate) {
        filter = newFilter;
        if (selectedNode != null) {
            filter.setSequent(selectedNode.sequent());
        }
        if (forceUpdate) {
            printSequent();
        }
    }

    /**
     * Does the active print filter hide formulas from the sequent (Swing
     * {@code SequentView.isHiding}).
     *
     * @return {@code true} iff at least one formula is not shown
     */
    public boolean isHiding() {
        Sequent originalSequent = filter.getOriginalSequent();
        if (originalSequent == null) {
            return false;
        }
        int filteredSize =
            (filter.getFilteredAntec() == null ? 0 : filter.getFilteredAntec().size())
                    + (filter.getFilteredSucc() == null ? 0 : filter.getFilteredSucc().size());
        return originalSequent.size() != filteredSize;
    }

    /** Shows or hides the hide-warning banner (Swing {@code updateHidingProperty}). */
    private void updateHideWarning() {
        boolean hiding = isHiding();
        hideWarning.setVisible(hiding);
        hideWarning.setManaged(hiding);
    }

    /**
     * Runs the search for the current field text (Swing {@code search()}): the sequent is always
     * re-printed (Swing {@code SequentViewSearchBar.search}: "search always does a repaint") — an
     * active search filter (Hide/Regroup mode) re-filters the sequent with the query, the
     * identity filter of the Highlight mode re-prints the plain sequent so that formulas hidden
     * by a previous mode reappear. Then all matches of the query are highlighted in the rendered
     * text. An invalid regular expression and a query without matches switch the field to the
     * alert styling.
     */
    private void runSearch() {
        searchMatches.clear();
        searchResultPos = -1;
        String text = searchField.getText();
        if (filter instanceof SearchSequentPrintFilter searchFilter && printer != null
                && selectedNode != null) {
            searchFilter.setRegex(regexToggle.isSelected());
            searchFilter.setLogicPrinter(printer);
            // an invalid regular expression leaves the filter unchanged: the Swing bar
            // re-filters with the broken pattern and then crashes printing it (latent Swing
            // bug); here the previous filter state stays and the field alerts below
            if (createPattern(text) != null) {
                searchFilter.setSearchString(text);
            }
        }
        if (printer != null && selectedNode != null) {
            printSequent();
        }
        if (text.isEmpty()) {
            setAlert(false);
            rebuildRuns();
            return;
        }
        Pattern pattern = createPattern(text);
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

    /**
     * Creates the search pattern for the current field text (Swing
     * {@code SearchSequentPrintFilter.createPattern}), {@code null} if it is not a valid regular
     * expression.
     */
    private Pattern createPattern(String text) {
        try {
            return SearchSequentPrintFilter.createPattern(text, regexToggle.isSelected());
        } catch (IllegalRegexException e) {
            LOGGER.debug("runSearch: text={} invalid regex", text);
            return null;
        }
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
     * menu: selects the search mode in the search bar's combo (Swing
     * {@code SequentViewSearchBar.setSearchMode}, SequentViewSearchBar.java:82-84:
     * {@code searchModeBox.setSelectedItem(mode)}). The combo's own listener applies the mode
     * ({@link #applySearchMode(SearchMode)}) and re-runs the search, so selecting here is
     * sufficient. Entry point of the "Proof > Search Mode" submenu (Swing
     * {@code SearchModeChangeAction}, MainWindow.createProofMenu :1125-1131).
     *
     * @param mode the search mode to select (Highlight/Hide/Regroup), must not be {@code null}
     */
    public void setSearchMode(SearchMode mode) {
        searchModeBox.getSelectionModel().select(mode);
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

        // syntax highlight intervals (one category wins per segment, see priority below)
        List<SequentSyntaxHighlighterF.Highlight> syntax = syntaxHighlights;

        // overlay intervals: the clicked term plus the search matches; the current search
        // match is styled stronger (Swing highlight_1 vs highlight_2)
        List<int[]> overlays = new ArrayList<>();
        List<String> overlayStyles = new ArrayList<>();
        if (highlightedRange != null) {
            int start = Math.clamp(highlightedRange.start(), 0, printed.length());
            int end = Math.clamp(highlightedRange.start() + highlightedRange.length(), start,
                printed.length());
            if (end > start) {
                overlays.add(new int[] { start, end });
                overlayStyles.add("sequent-term-highlight");
            }
        }
        for (int i = 0; i < searchMatches.size(); i++) {
            overlays.add(searchMatches.get(i));
            overlayStyles.add(i == searchResultPos ? "sequent-search-match-current"
                    : "sequent-search-match");
        }
        if (syntax.isEmpty() && overlays.isEmpty()) {
            addRun(printed, font, "sequent-text");
            return;
        }

        // split the text at every interval boundary; each segment is then uniformly covered by
        // the intervals that overlap it
        TreeSet<Integer> points = new TreeSet<>();
        points.add(0);
        points.add(printed.length());
        for (SequentSyntaxHighlighterF.Highlight highlight : syntax) {
            if (highlight.start() > 0 && highlight.start() < printed.length()) {
                points.add(highlight.start());
            }
            if (highlight.end() > 0 && highlight.end() < printed.length()) {
                points.add(highlight.end());
            }
        }
        for (int[] overlay : overlays) {
            if (overlay[0] > 0 && overlay[0] < printed.length()) {
                points.add(overlay[0]);
            }
            if (overlay[1] > 0 && overlay[1] < printed.length()) {
                points.add(overlay[1]);
            }
        }

        // sweep over the segments: the syntax intervals starting at or before the segment become
        // active, ended ones drop out; the winner is the lowest priority among the active ones
        // (mirrors the innermost-wins nesting of the Swing HTML spans)
        List<SequentSyntaxHighlighterF.Highlight> active = new ArrayList<>();
        int pointer = 0;
        Integer[] sorted = points.toArray(new Integer[0]);
        for (int p = 0; p < sorted.length - 1; p++) {
            int start = sorted[p];
            int end = sorted[p + 1];
            while (pointer < syntax.size() && syntax.get(pointer).start() <= start) {
                active.add(syntax.get(pointer++));
            }
            active.removeIf(highlight -> highlight.end() <= start);
            List<String> styles = new ArrayList<>();
            styles.add("sequent-text");
            if (!active.isEmpty()) {
                SequentSyntaxHighlighterF.Kind winner = active.get(0).kind();
                int winnerPriority = SequentSyntaxHighlighterF.priority(winner);
                for (SequentSyntaxHighlighterF.Highlight highlight : active) {
                    int priority = SequentSyntaxHighlighterF.priority(highlight.kind());
                    if (priority < winnerPriority) {
                        winnerPriority = priority;
                        winner = highlight.kind();
                    }
                }
                styles.add(SequentSyntaxHighlighterF.styleClass(winner));
            }
            for (int i = 0; i < overlays.size(); i++) {
                int[] overlay = overlays.get(i);
                if (overlay[0] <= start && end <= overlay[1]) {
                    styles.add(overlayStyles.get(i));
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
        clearHover();
        updateHideWarning();
        textFlow.getChildren().clear();
        printed = null;
        updateOverlay.getChildren().clear();
        updateRectCount = 0;
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
        // the bar was closed before (mode Highlight); make the baseline deterministic
        searchModeBox.getSelectionModel().select(SearchMode.HIGHLIGHT);
        if (!query.equals(searchField.getText())) {
            searchField.setText(query);
        } else {
            runSearch();
        }
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
     * Development self-test (M2): exercises the search modes like the Swing search bar. In the
     * Highlight mode the plain sequent with all matches is the baseline; the Hide mode must print
     * only the formulas matching the query (a subset of the baseline formulas, hiding = fewer
     * characters); the Regroup mode must print the same formulas with the matching ones grouped
     * at the sequent arrow (antecedent: matching at the end, succedent: matching at the start,
     * like Swing's {@code RegroupSequentPrintFilter} reorders). The baseline must reproduce the
     * original sequent exactly — a half that is empty in the original sequent stays legitimately
     * empty (e.g. the Agatha demo has no antecedent formula); with a query that matches every
     * formula Hide and Regroup are no-ops and the report marks them {@code vacuous}. Restores the
     * plain view.
     * <p>
     * The modes can only be exercised on a sequent with at least two formulas; the displayed node
     * of a fresh demo proof (the root) has a single one. The test therefore runs on
     * {@link #findModeTestNode()} and restores the display of the original node afterwards, like
     * the Swing bar closing leaves the selected node displayed.
     *
     * @param query the query to search for
     * @return a one-line report, {@code "... PASS"} if the modes behave as expected
     */
    public String verifySearchModes(String query) {
        if (printed == null || selectedNode == null) {
            return "no printed sequent";
        }
        Node originalNode = selectedNode;
        Node testNode = findModeTestNode();
        if (testNode != null && testNode != originalNode) {
            display(testNode);
        }
        showSearchBar();
        // baseline: Highlight mode = the plain printing with the matches highlighted
        SequentPrintFilter baselineFilter = new IdentitySequentPrintFilter();
        setSequentFilter(baselineFilter, true);
        searchModeBox.getSelectionModel().select(SearchMode.HIGHLIGHT);
        if (!query.equals(searchField.getText())) {
            searchField.setText(query);
        } else {
            runSearch();
        }
        int highlightChars = printed.length();
        int highlightMatches = searchMatches.size();
        String highlightText = printed;
        List<SequentFormula> highlightAntec = filterFormulas(filter.getFilteredAntec());
        List<SequentFormula> highlightSucc = filterFormulas(filter.getFilteredSucc());

        // Hide: only the formulas matching the query are printed
        searchModeBox.getSelectionModel().select(SearchMode.HIDE);
        int hideChars = printed.length();
        int hideMatches = searchMatches.size();
        boolean hideHiding = isHiding();
        List<SequentFormula> matchingAntec = filterFormulas(filter.getFilteredAntec());
        List<SequentFormula> matchingSucc = filterFormulas(filter.getFilteredSucc());
        boolean hideSubset = isSubsequence(highlightAntec, matchingAntec)
                && isSubsequence(highlightSucc, matchingSucc);

        // Regroup: the same formulas, the matching ones regrouped around the arrow
        searchModeBox.getSelectionModel().select(SearchMode.REGROUP);
        int regroupChars = printed.length();
        int regroupMatches = searchMatches.size();
        List<SequentFormula> regroupAntec = filterFormulas(filter.getFilteredAntec());
        List<SequentFormula> regroupSucc = filterFormulas(filter.getFilteredSucc());
        boolean regroupSame = sameFormulas(highlightAntec, regroupAntec)
                && sameFormulas(highlightSucc, regroupSucc);
        boolean regroupOrder = expectedRegroup(highlightAntec, matchingAntec, false)
                .equals(regroupAntec)
                && expectedRegroup(highlightSucc, matchingSucc, true).equals(regroupSucc);
        boolean regrouped = !printed.equals(highlightText);

        // restore the plain view (Highlight mode + closed bar), as the Swing bar closes
        hideSearchBar();
        if (testNode != null && testNode != originalNode) {
            display(originalNode);
        }
        // the baseline must be the full original sequent (the identity filter keeps every
        // formula; a half that is empty in the original sequent stays legitimately empty —
        // e.g. the Agatha demo sequent has no antecedent because KeY does not split the
        // top-level implication of the problem statement)
        List<SequentFormula> originalAntec = sequentFormulas(baselineFilter.getOriginalSequent(),
            true);
        List<SequentFormula> originalSucc = sequentFormulas(baselineFilter.getOriginalSequent(),
            false);
        boolean baselineOk = highlightMatches > 0 && sameFormulas(originalAntec, highlightAntec)
                && sameFormulas(originalSucc, highlightSucc);
        boolean hideOk = hideChars <= highlightChars && hideMatches > 0
                && hideHiding == (hideChars < highlightChars) && hideSubset;
        boolean regroupOk = regroupSame && regroupOrder && regroupMatches == highlightMatches;
        boolean pass = baselineOk && hideOk && regroupOk;
        // vacuous: the query matched every formula, Hide and Regroup cannot change anything
        boolean vacuous = hideChars == highlightChars && regroupChars == highlightChars;
        return "query=" + query + " node=" + (testNode != null ? testNode.serialNr() : -1)
            + " highlight chars=" + highlightChars + " matches="
            + highlightMatches + " antec=" + highlightAntec.size() + " succ="
            + highlightSucc.size() + " | hide chars=" + hideChars + " matches=" + hideMatches
            + " antec=" + matchingAntec.size() + " succ=" + matchingSucc.size() + " hiding="
            + hideHiding + " subset=" + hideSubset + " | regroup chars=" + regroupChars
            + " matches=" + regroupMatches + " antec=" + regroupAntec.size() + " succ="
            + regroupSucc.size() + " same=" + regroupSame + " order=" + regroupOrder
            + " regrouped=" + regrouped + " | baselineOk=" + baselineOk + " hideOk=" + hideOk
            + " regroupOk=" + regroupOk + " vacuous=" + vacuous + " "
            + (pass ? "PASS" : "FAIL");
    }

    /**
     * Finds the node to run the search mode self test on: the node with the most sequent formulas
     * in the subtree of the displayed node — or, if even that subtree has no multi-formula node,
     * of the whole proof, falling back to the displayed node itself. The richest node is wanted
     * because the modes can only be exercised on a sequent with several formulas, and the
     * displayed node of a demo proof is often poor (the root has a single formula; after the tree
     * search verification the selection rests on a two-formula node).
     *
     * @return the test node (never {@code null} if a node is displayed)
     */
    private Node findModeTestNode() {
        if (selectedNode == null) {
            return null;
        }
        Node best = findRichestNode(selectedNode);
        if (best == null && proof != null) {
            best = findRichestNode(proof.root());
        }
        return best != null ? best : selectedNode;
    }

    /**
     * @return the node with the most sequent formulas in the subtree of the given node where at
     *         least two formulas exist ({@code null} if there is none; pre-order walk, the first
     *         node wins on ties)
     */
    private static Node findRichestNode(Node node) {
        ArrayDeque<Node> stack = new ArrayDeque<>();
        stack.push(node);
        Node best = null;
        int bestSize = 1;
        while (!stack.isEmpty()) {
            Node current = stack.pop();
            int size = current.sequent().size();
            if (size > bestSize) {
                best = current;
                bestSize = size;
            }
            for (int i = 0; i < current.childrenCount(); i++) {
                stack.push(current.child(i));
            }
        }
        return best;
    }

    /**
     * Development self-test (M2): verifies the update-highlight overlays of the current printing
     * (Swing {@code CurrentGoalView.updateUpdateHighlights}): every update range of the position
     * table must be displayed as one translucent rectangle whose shape lies inside the text flow
     * bounds. Requires a sequent that prints update operators (e.g. a program verification goal
     * after symbolic execution); a plain sequent reports {@code ranges=0 ... FAIL}.
     *
     * @return a one-line report, {@code "... PASS"} if the overlays exist with valid geometry
     */
    public String verifyUpdateHighlights() {
        if (printed == null) {
            return "no printed sequent";
        }
        textFlow.applyCss();
        textFlow.layout();
        InitialPositionTable table = getInitialPositionTable();
        Range[] ranges = table == null ? new Range[0] : table.getUpdateRanges();
        boolean geometryOk = ranges.length > 0;
        for (Range range : ranges) {
            int start = Math.clamp(range.start(), 0, printed.length());
            int end = Math.clamp(range.end(), start, printed.length());
            double minX = Double.POSITIVE_INFINITY;
            double minY = Double.POSITIVE_INFINITY;
            double maxX = Double.NEGATIVE_INFINITY;
            double maxY = Double.NEGATIVE_INFINITY;
            for (PathElement element : textFlow.getRangeShape(start, end, true)) {
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
            geometryOk &= Double.isFinite(minX) && maxX > minX && maxY > minY
                    && minX >= -1 && minY >= -1 && maxX <= textFlow.getWidth() + 1
                    && maxY <= textFlow.getHeight() + 1;
        }
        boolean pass = ranges.length > 0 && updateRectCount == ranges.length && geometryOk;
        return "ranges=" + ranges.length + " rects=" + updateRectCount + " geometryOk="
            + geometryOk + " " + (pass ? "PASS" : "FAIL");
    }

    /**
     * @return the original formulas of the given filter entries, in printing order
     */
    private static List<SequentFormula> filterFormulas(
            ImmutableList<SequentPrintFilterEntry> entries) {
        List<SequentFormula> formulas = new ArrayList<>();
        if (entries != null) {
            for (SequentPrintFilterEntry entry : entries) {
                formulas.add(entry.getOriginalFormula());
            }
        }
        return formulas;
    }

    /**
     * @return the formulas of the given sequent half, in printing order
     */
    private static List<SequentFormula> sequentFormulas(Sequent sequent, boolean antecedent) {
        List<SequentFormula> formulas = new ArrayList<>();
        if (sequent != null) {
            Semisequent semisequent = antecedent ? sequent.antecedent() : sequent.succedent();
            for (Iterator<SequentFormula> it = semisequent.iterator(); it.hasNext();) {
                formulas.add(it.next());
            }
        }
        return formulas;
    }

    /**
     * @return {@code true} iff {@code sub} is a subsequence of {@code list} (same formula
     *         objects, same order) — the Hide filter keeps the matching formulas in order
     */
    private static boolean isSubsequence(List<SequentFormula> list, List<SequentFormula> sub) {
        if (sub.size() > list.size()) {
            return false;
        }
        int i = 0;
        for (SequentFormula formula : sub) {
            while (i < list.size() && list.get(i) != formula) {
                i++;
            }
            if (i == list.size()) {
                return false;
            }
            i++;
        }
        return true;
    }

    /**
     * @return {@code true} iff both lists contain the same formula objects (any order) — the
     *         Regroup filter reorders but never drops formulas
     */
    private static boolean sameFormulas(List<SequentFormula> list, List<SequentFormula> other) {
        if (list.size() != other.size()) {
            return false;
        }
        List<SequentFormula> copy = new ArrayList<>(other);
        for (SequentFormula formula : list) {
            if (!removeRef(copy, formula)) {
                return false;
            }
        }
        return copy.isEmpty();
    }

    /**
     * The regrouped order the Swing {@code RegroupSequentPrintFilter.filterSequent} computes:
     * iterating the original order, a matching formula is appended (antecedent) resp. prepended
     * (succedent), a non-matching one prepended (antecedent) resp. appended (succedent) — so the
     * matching formulas end up grouped at the sequent arrow.
     *
     * @param base the formulas in original order (the Highlight mode printing)
     * @param matching the formulas matching the query (the Hide mode printing), as a subsequence
     *        of {@code base}
     * @param matchingAtStart whether the matching formulas belong at the arrow-adjacent start of
     *        the list (succedent) or at its end (antecedent)
     * @return the expected regrouped formula list
     */
    private static List<SequentFormula> expectedRegroup(List<SequentFormula> base,
            List<SequentFormula> matching, boolean matchingAtStart) {
        ArrayDeque<SequentFormula> deque = new ArrayDeque<>();
        for (SequentFormula formula : base) {
            boolean match = containsRef(matching, formula);
            if (match == matchingAtStart) {
                deque.addFirst(formula);
            } else {
                deque.addLast(formula);
            }
        }
        return new ArrayList<>(deque);
    }

    private static boolean containsRef(List<SequentFormula> list, SequentFormula formula) {
        for (SequentFormula candidate : list) {
            if (candidate == formula) {
                return true;
            }
        }
        return false;
    }

    private static boolean removeRef(List<SequentFormula> list, SequentFormula formula) {
        for (int i = 0; i < list.size(); i++) {
            if (list.get(i) == formula) {
                list.remove(i);
                return true;
            }
        }
        return false;
    }

    /**
     * Development self-test (M2): verifies the syntax highlighting of the current printing — the
     * intervals must be valid ranges of the printed text, at least the sequent arrow must be
     * highlighted, and the category of every interval must map to a style class.
     *
     * @return a one-line report, {@code "... PASS"} if the highlighting behaves as expected
     */
    public String verifySyntaxHighlighting() {
        if (printed == null) {
            return "no printed sequent";
        }
        int arrows = 0;
        int progvars = 0;
        boolean inBounds = true;
        for (SequentSyntaxHighlighterF.Highlight highlight : syntaxHighlights) {
            inBounds &= highlight.start() >= 0 && highlight.end() > highlight.start()
                    && highlight.end() <= printed.length();
            if (highlight.kind() == SequentSyntaxHighlighterF.Kind.ARROW) {
                arrows++;
            }
            if (highlight.kind() == SequentSyntaxHighlighterF.Kind.PROGVAR) {
                progvars++;
            }
        }
        boolean pass = inBounds && !syntaxHighlights.isEmpty() && arrows >= 1;
        return "intervals=" + syntaxHighlights.size() + " arrows=" + arrows + " progvars="
            + progvars + " inBounds=" + inBounds + " " + (pass ? "PASS" : "FAIL");
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
