/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.originlabels;

import java.util.Objects;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Tooltip;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.StackPane;
import javafx.scene.shape.Path;
import javafx.scene.text.Font;
import javafx.scene.text.HitInfo;
import javafx.scene.text.Text;
import javafx.scene.text.TextFlow;
import javafx.stage.StageStyle;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.nodeinfo.NodeInfoVisualizerF;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentPrintFilterEntry;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.ShowSelectedSequentPrintFilter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.util.pp.UnbalancedBlocksException;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * JavaFX port of the Swing {@code de.uka.ilkd.key.gui.originlabels.OriginTermLabelVisualizer}
 * (a {@code NodeInfoVisualizer}): visualizes the {@link OriginTermLabel}s of a term and its
 * sub-terms for one node of the proof.
 * <p>
 * The window layout follows the Swing original: a head pane with the node link ("Node: &lt;n&gt;:
 * &lt;name&gt;", clicking selects the node in the mediator — with the Swing confirmation dialog
 * when the node's proof is not the selected one) and the proof name; a split pane with (a) the
 * origin tree — one row per (sub-)term, showing the short-printed term on the left and the
 * origin's specification type on the right, with a tooltip containing the origin and the origins
 * of the (former) sub-terms — and (b) the term view, a read-only sequent view printing only the
 * selected formula ({@code ShowSelectedSequentPrintFilter}) or the whole sequent, through the
 * ported {@link TermViewLogicPrinterF}. Selecting a tree row highlights the corresponding term
 * in the view (Swing {@code setUserSelectionHighlight}, orange rectangle) and clicking a term in
 * the view selects the corresponding tree row (Swing mouse listener). Like in Swing, the origin
 * labels themselves are <em>not</em> printed inside the term view
 * ({@code TermLabelVisibilityManager} hides {@code OriginTermLabel.NAME}); the origins are shown
 * by the tree and the tooltips.
 * <p>
 * The node link stays live: proof-tree changes update it, and a deleted node disables the link
 * and unregisters the window (Swing {@code updateNodeLink} with the rule-app/proof-tree/disposed
 * listeners; here the proof-tree and proof-disposed listeners are registered — the rule-app
 * listener adds no extra information beyond the proof-tree events).
 * <p>
 * Presentation deviations: the Swing {@code JSplitPane} divider starts collapsed to the right
 * ({@code setDividerLocation(1.0)}); the FX window opens with the tree and view side by side
 * (the information is the same). HTML tooltips become plain multi-line text, the Swing
 * {@code JTree} becomes a JavaFX {@link TreeView} and the origin highlight color is the CSS
 * class {@code origin-visualizer-highlight} (Swing {@code Color.ORANGE}).
 */
public final class OriginTermLabelVisualizerF extends NodeInfoVisualizerF {

    private static final Logger LOGGER = LoggerFactory.getLogger(OriginTermLabelVisualizerF.class);

    /** The title for the origin information for the selected term (Swing constant). */
    public static final String ORIGIN_INFO_TITLE = "Origin information";

    /** The title for the selected term's origin (Swing constant). */
    public static final String ORIGIN_TITLE = "Origin of formula";

    /**
     * The title for the origin of the selected term's sub-terms and former sub-terms (Swing
     * constant).
     */
    public static final String SUBTERM_ORIGINS_TITLE =
        "Origins of (former) subformulas and subterms";

    /** Window size (the Swing visualizer is hosted in the source view frame; free size here). */
    private static final double WIDTH = 900;
    private static final double HEIGHT = 600;

    /** services */
    private final Services services;

    /** top-level position cache ({@code PosInTerm.getTopLevel()}). */
    private static final org.key_project.logic.PosInTerm topPos =
        org.key_project.logic.PosInTerm.getTopLevel();

    /** The position of the term being shown in this window (Swing {@code termPio}). */
    private final PosInOccurrence termPio;

    /** The sequent containing the term being shown in this window (Swing {@code sequent}). */
    private final Sequent sequent;

    /** the origin tree (Swing {@code tree}). */
    private final TreeView<TreeNodeF> tree = new TreeView<>();

    /** the term view (Swing {@code view}, a specialized SequentView). */
    private final TermViewF view;

    /** the currently highlighted position (Swing {@code highlight}). */
    private PosInOccurrence highlight;

    /** the node link button (Swing {@code nodeLinkButton}). */
    private final Button nodeLinkButton = new Button();

    /** the node link action state, mirrored to the button (Swing {@code nodeLinkAction}). */
    private final StringProperty nodeLinkText = new SimpleStringProperty();

    /** the mediator entry point for the node link (Swing {@code MainWindow.getInstance()}). */
    private final MainWindowF mainWindow;

    /** updates the node link on proof changes (Swing {@code proofTreeListener}). */
    private final ProofTreeListener proofTreeListener = new ProofTreeAdapter() {
        @Override
        public void proofStructureChanged(ProofTreeEvent e) {
            updateNodeLink();
        }

        @Override
        public void proofPruned(ProofTreeEvent e) {
            updateNodeLink();
        }

        @Override
        public void proofGoalsChanged(ProofTreeEvent e) {
            updateNodeLink();
        }

        @Override
        public void proofExpanded(ProofTreeEvent e) {
            updateNodeLink();
        }
    };

    /** updates the node link when the proof is disposed (Swing {@code proofDisposedListener}). */
    private final ProofDisposedListener proofDisposedListener = new ProofDisposedListener() {
        @Override
        public void proofDisposing(ProofDisposedEvent e) {
            // nothing
        }

        @Override
        public void proofDisposed(ProofDisposedEvent e) {
            updateNodeLink();
        }
    };

    /**
     * Creates a new origin visualizer window.
     *
     * @param mainWindow the main window (mediator access for the node link)
     * @param pos the position of the term whose origin shall be visualized ({@code null} shows
     *        the whole sequent, Swing {@code ShowOriginAction} walks up to the formula first)
     * @param node the node representing the proof state for which the term's origins shall be
     *        visualized
     * @param services services
     */
    public OriginTermLabelVisualizerF(MainWindowF mainWindow, PosInOccurrence pos, Node node,
            Services services) {
        super(node,
            "Origin for node " + node.serialNr() + ": " + (pos == null ? "whole sequent"
                    : de.uka.ilkd.key.pp.LogicPrinter
                            .quickPrintTerm((JTerm) pos.subTerm(), services)
                            .replaceAll("\\s+", " ")),
            "Node " + node.serialNr());
        this.mainWindow = mainWindow;
        this.services = services;
        this.termPio = pos;
        this.sequent = node.sequent();
        this.view = new TermViewF();

        setTitle(getLongName());
        initStyle(StageStyle.DECORATED);
        if (mainWindow.getStage() != null) {
            initOwner(mainWindow.getStage());
        }

        BorderPane root = new BorderPane();
        root.setTop(createHeadPane());
        root.setCenter(createBodyPane());
        Scene scene = new Scene(root, WIDTH, HEIGHT);
        ThemeManager.getInstance().manage(scene);
        setScene(scene);
        setOnCloseRequest(e -> dispose());

        node.proof().addProofTreeListener(proofTreeListener);
        node.proof().addProofDisposedListener(proofDisposedListener);
        updateNodeLink();
    }

    /** The head pane: node link + proof name (Swing {@code initHeadPane}). */
    private HBox createHeadPane() {
        nodeLinkButton.textProperty().bind(nodeLinkText);
        nodeLinkButton.setOnAction(e -> selectNode());
        Label proofLabel = new Label("Proof: \"" + getNode().proof().name() + "\"");
        HBox head = new HBox(20);
        head.setAlignment(Pos.CENTER_LEFT);
        head.getChildren().addAll(new Label("Node: "), nodeLinkButton, proofLabel);
        return head;
    }

    /** The body: origin tree (left) and term view (right) (Swing {@code initTree/initView}). */
    private SplitPane createBodyPane() {
        tree.setRoot(buildTreeModel());
        tree.setCellFactory(v -> new OriginTreeCell());
        tree.getSelectionModel().selectedItemProperty().addListener((obs, oldItem, newItem) -> {
            highlight = newItem == null ? null : newItem.getValue().pos();
            view.highlightTerm(highlight);
        });

        Label treeTitle = new Label(borderTitle() + " as tree");
        Label viewTitle = new Label(borderTitle());
        treeTitle.getStyleClass().add("dialog-section-title");
        viewTitle.getStyleClass().add("dialog-section-title");

        BorderPane treePane = new BorderPane(tree);
        treePane.setTop(treeTitle);
        BorderPane viewPane = new BorderPane(view);
        viewPane.setTop(viewTitle);
        SplitPane body = new SplitPane(treePane, viewPane);
        SplitPane.setResizableWithParent(treePane, Boolean.TRUE);
        return body;
    }

    /** The split-pane titles (Swing {@code borderTitle}: the selection side). */
    private String borderTitle() {
        if (termPio == null) {
            return "selected sequent";
        }
        return termPio.isInAntec() ? "selected formula in antecedent"
                : "selected formula in succedent";
    }

    /** The tree model root (Swing {@code buildModel(PosInOccurrence)}). */
    private TreeItem<TreeNodeF> buildTreeModel() {
        TreeItem<TreeNodeF> root = new TreeItem<>(new TreeNodeF(termPio));
        fillChildren(root, termPio);
        return root;
    }

    /** Recursive tree model construction (Swing {@code buildModel(TreeNode, Pos, TreeModel)}). */
    private void fillChildren(TreeItem<TreeNodeF> parent, PosInOccurrence parentPos) {
        if (parentPos == null) {
            for (SequentFormula child : sequent.antecedent()) {
                PosInOccurrence childPos = new PosInOccurrence(child, topPos, true);
                TreeItem<TreeNodeF> childItem = new TreeItem<>(new TreeNodeF(childPos));
                parent.getChildren().add(childItem);
                fillChildren(childItem, childPos);
            }
            for (SequentFormula child : sequent.succedent()) {
                PosInOccurrence childPos = new PosInOccurrence(child, topPos, false);
                TreeItem<TreeNodeF> childItem = new TreeItem<>(new TreeNodeF(childPos));
                parent.getChildren().add(childItem);
                fillChildren(childItem, childPos);
            }
        } else {
            var children = parentPos.subTerm().subs();
            for (int i = 0; i < children.size(); ++i) {
                PosInOccurrence childPos = parentPos.down(i);
                TreeItem<TreeNodeF> childItem = new TreeItem<>(new TreeNodeF(childPos));
                parent.getChildren().add(childItem);
                fillChildren(childItem, childPos);
            }
        }
    }

    /**
     * The node link action (Swing {@code nodeLinkAction}): selects the node in the mediator,
     * asking when the node's proof is not the currently selected one.
     */
    private void selectNode() {
        var selectionModel = mainWindow.getSelectionModel();
        Node node = getNode();
        if (node == null) {
            return;
        }
        if (!selectionModel.getSelectedProof().equals(node.proof())) {
            Alert alert = new Alert(Alert.AlertType.CONFIRMATION);
            alert.setTitle("Switch Proof?");
            alert.setHeaderText(null);
            alert.setContentText("The proof containing this node is not currently selected."
                + " Do you want to select it?");
            alert.initOwner(this);
            if (alert.showAndWait().orElse(ButtonType.CANCEL) != ButtonType.OK) {
                return;
            }
            selectionModel.setSelectedProof(node.proof());
        }
        selectionModel.setSelectedNode(node);
    }

    /**
     * Keeps the node link current (Swing {@code updateNodeLink}): "DELETED NODE" + unregister
     * when the node is no longer in the proof, the serial number/name otherwise.
     */
    private void updateNodeLink() {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(this::updateNodeLink);
            return;
        }
        Node node = getNode();
        if (node == null) {
            return;
        }
        if (node.proof().isDisposed() || !node.proof().find(node)) {
            nodeLinkText.set("DELETED NODE");
            nodeLinkButton.setDisable(true);
            unregister(this);
        } else {
            nodeLinkText.set(node.serialNr() + ": " + node.name());
        }
    }

    @Override
    public void dispose() {
        Node node = getNode();
        if (node != null && !node.proof().isDisposed()) {
            node.proof().removeProofTreeListener(proofTreeListener);
            node.proof().removeProofDisposedListener(proofDisposedListener);
        }
        view.dispose();
        super.dispose();
    }

    /**
     * @return whether the term view printed a non-empty text; used by the self test
     */
    boolean viewPrinted() {
        return view.hasText();
    }

    /**
     * @return the number of rows of the origin tree (all levels); used by the
     *         {@code key.fx.verify.lemmaorigin} self test
     */
    int treeRowCount() {
        return countRows(tree.getRoot());
    }

    private static int countRows(TreeItem<?> item) {
        int result = 1;
        for (TreeItem<?> child : item.getChildren()) {
            result += countRows(child);
        }
        return result;
    }

    // ------------------------------------------------------------------
    // origin tree helpers
    // ------------------------------------------------------------------

    /**
     * A tree node: the position of a (sub-)term (Swing {@code TreeNode extends
     * DefaultMutableTreeNode}).
     */
    private static final class TreeNodeF {
        private final PosInOccurrence pos;
        private final JTerm term;

        TreeNodeF(PosInOccurrence pos) {
            this.pos = pos;
            this.term = pos == null ? null : (JTerm) pos.subTerm();
        }

        PosInOccurrence pos() {
            return pos;
        }
    }

    /** The tree cell: term text left, origin spec type right, origin tooltip. */
    private final class OriginTreeCell extends TreeCell<TreeNodeF> {

        private final HBox box = new HBox(10);
        private final Text termText = new Text();
        private final Text originText = new Text();

        OriginTreeCell() {
            Region spacer = new Region();
            HBox.setHgrow(spacer, Priority.ALWAYS);
            box.getChildren().addAll(termText, spacer, originText);
            box.prefWidthProperty().bind(widthProperty().subtract(90));
            box.setAlignment(Pos.CENTER_LEFT);
            setGraphic(box);
            setText(null);
        }

        @Override
        protected void updateItem(TreeNodeF item, boolean empty) {
            super.updateItem(item, empty);
            if (empty || item == null) {
                setGraphic(null);
                setTooltip(null);
                return;
            }
            termText.setText(shortTermText(item.term));
            termText.setFont(ConfigF.DEFAULT.monoFont());
            originText.getStyleClass().add("origin-visualizer-origin");
            originText.setFont(ConfigF.DEFAULT.monoFont());
            Origin origin = item.pos == null ? null : OriginTermLabel.getOrigin(item.pos);
            originText.setText(origin == null ? "" : shortOriginText(origin));
            setGraphic(box);
            setTooltip(new Tooltip(tooltipText(item.pos)));
        }

        /** The short origin text (Swing {@code getShortOriginText}: the specification type). */
        private String shortOriginText(Origin origin) {
            return origin.specType.toString();
        }
    }

    /**
     * The short-printed term (Swing {@code CellRenderer.getShortTermText}): the first line of
     * the pretty-printed term (the whole sequent for a {@code null} term), whitespace-flattened.
     */
    private String shortTermText(JTerm term) {
        String text;
        if (term == null) {
            text = de.uka.ilkd.key.pp.LogicPrinter.quickPrintSequent(sequent, services);
        } else {
            text = de.uka.ilkd.key.pp.LogicPrinter.quickPrintTerm(term, services);
        }
        int endIndex = text.indexOf('\n');
        if (endIndex != text.length() - 1 && endIndex != -1) {
            return text.substring(0, endIndex).replaceAll("\\s+", " ") + " ...";
        }
        return text.replaceAll("\\s+", " ");
    }

    /**
     * The tooltip text for a position (Swing {@code getTooltipText}, HTML becomes plain text):
     * the origin of the term and the origins of its (former) sub-terms.
     */
    private String tooltipText(PosInOccurrence pio) {
        if (pio == null) {
            return null;
        }
        OriginTermLabel label =
            (OriginTermLabel) ((JTerm) pio.subTerm()).getLabel(OriginTermLabel.NAME);
        Origin origin = OriginTermLabel.getOrigin(pio);
        StringBuilder result = new StringBuilder("Origin of selected term: ")
                .append(origin == null ? "" : origin);
        result.append("\nOrigin of (former) sub-terms:\n");
        if (label != null) {
            for (Origin subOrigin : label.getSubtermOrigins()) {
                result.append(subOrigin).append('\n');
            }
        }
        return result.toString();
    }

    // ------------------------------------------------------------------
    // the term view (Swing inner class TermView + TermViewLogicPrinter)
    // ------------------------------------------------------------------

    /**
     * Converts a pio on the printed (filtered) sequent to a pio on {@link #termPio}'s term
     * (Swing {@code convertPio}).
     */
    private PosInOccurrence convertPio(PosInOccurrence pio) {
        if (termPio == null) {
            return pio;
        } else if (pio == null) {
            return new PosInOccurrence(termPio.sequentFormula(), termPio.posInTerm(),
                termPio.isInAntec());
        }
        org.key_project.logic.PosInTerm completePos = termPio.posInTerm();
        org.key_project.logic.IntIterator it = pio.posInTerm().iterator();
        while (it.hasNext()) {
            completePos = completePos.down(it.next());
        }
        return new PosInOccurrence(termPio.sequentFormula(), completePos, termPio.isInAntec());
    }

    /**
     * The term view pane (Swing inner class {@code TermView extends SequentView}): prints the
     * selected formula (or the whole sequent) with all term labels except the origin labels,
     * supports the highlight of a selected position and reports clicked positions.
     */
    private final class TermViewF extends BorderPane {

        private final ScrollPane scrollPane = new ScrollPane();
        private final StackPane content = new StackPane();
        private final javafx.scene.layout.Pane highlightPane = new javafx.scene.layout.Pane();
        private final TextFlow textFlow = new TextFlow();
        private SequentViewLogicPrinter printer;
        private SequentPrintFilter filter;
        private String printed;
        private InitialPositionTable posTable;

        TermViewF() {
            highlightPane.getStyleClass().add("sequent-overlay");
            highlightPane.setMouseTransparent(true);
            highlightPane.setMaxSize(Double.MAX_VALUE, Double.MAX_VALUE);
            content.getChildren().addAll(highlightPane, textFlow);
            scrollPane.setContent(content);
            scrollPane.setFitToWidth(true);
            setCenter(scrollPane);
            textFlow.getStyleClass().add("sequent-view-flow");
            textFlow.setPadding(new javafx.geometry.Insets(6));
            textFlow.setOnMouseClicked(this::handleClick);
            print();
        }

        /** Prints the term view (Swing {@code view.printSequent()}). */
        void print() {
            NotationInfo ni = new NotationInfo();
            if (services != null) {
                ni.refresh(services, NotationInfo.DEFAULT_PRETTY_SYNTAX,
                    NotationInfo.DEFAULT_UNICODE_ENABLED, NotationInfo.DEFAULT_HIDE_PACKAGE_PREFIX);
            }
            printer = new TermViewLogicPrinterF(termPio, ni, services);
            filter = termPio != null ? new ShowSelectedSequentPrintFilter(termPio)
                    : new IdentitySequentPrintFilter();
            filter.setSequent(sequent);
            printer.update(filter, PosTableLayouter.DEFAULT_LINE_WIDTH);
            printed = printer.result();
            posTable = printer.layouter().getInitialPositionTable();
            rebuildRuns();
            highlightPane.getChildren().clear();
        }

        /** Renders the printed text as monospaced runs (the Swing view is an HTML editor pane). */
        private void rebuildRuns() {
            textFlow.getChildren().clear();
            if (printed == null || printed.isEmpty()) {
                return;
            }
            Font font = ConfigF.DEFAULT.monoFont();
            Text run = new Text(printed);
            run.getStyleClass().add("sequent-text");
            run.setFont(font);
            textFlow.getChildren().add(run);
        }

        /** Highlights the given position (Swing {@code setUserSelectionHighlight}). */
        void highlightTerm(PosInOccurrence pio) {
            highlightPane.getChildren().clear();
            if (pio == null || printed == null || posTable == null) {
                return;
            }
            ImmutableList<Integer> path = posTable.pathForPosition(pio, filter);
            if (path == null) {
                return;
            }
            Range range = posTable.rangeForPath(path);
            if (range == null || range.length() <= 0) {
                return;
            }
            int start = Math.clamp(range.start(), 0, printed.length());
            int end = Math.clamp(range.start() + range.length(), start, printed.length());
            if (end <= start) {
                return;
            }
            // shapes need a laid-out text flow
            textFlow.applyCss();
            textFlow.layout();
            Path rect = new Path(textFlow.getRangeShape(start, end, true));
            rect.getStyleClass().add("origin-visualizer-highlight");
            rect.setManaged(false);
            highlightPane.getChildren().add(rect);
        }

        /** Maps a click to a position and selects the corresponding tree row (Swing listener). */
        private void handleClick(MouseEvent event) {
            if (printed == null || posTable == null) {
                return;
            }
            javafx.geometry.Point2D local =
                textFlow.sceneToLocal(event.getSceneX(), event.getSceneY());
            HitInfo hit = textFlow.getHitInfo(local);
            int charIndex = hit == null ? -1 : hit.getCharIndex();
            if (charIndex < 0 || charIndex >= printed.length()) {
                highlight = null;
                view.highlightTerm(null);
                tree.getSelectionModel().clearSelection();
                return;
            }
            PosInSequent pis = posTable.getPosInSequent(charIndex, filter);
            PosInOccurrence pio = convertPio(pis == null ? null : pis.getPosInOccurrence());
            if (pio == null || Objects.equals(highlight, pio)) {
                highlight = null;
                view.highlightTerm(null);
                tree.getSelectionModel().clearSelection();
                return;
            }
            highlight = pio;
            view.highlightTerm(pio);
            selectTreeRow(pio);
        }

        /** Selects the tree row of the given position (Swing {@code getTreePath}). */
        private void selectTreeRow(PosInOccurrence pio) {
            TreeItem<TreeNodeF> found = findTreeItem(tree.getRoot(), pio);
            if (found != null) {
                // reveal the row like the Swing JTree selection does
                expandTo(found);
                tree.getSelectionModel().select(found);
            }
        }

        private void expandTo(TreeItem<TreeNodeF> item) {
            TreeItem<TreeNodeF> parent = item.getParent();
            while (parent != null) {
                parent.setExpanded(true);
                parent = parent.getParent();
            }
        }

        private TreeItem<TreeNodeF> findTreeItem(TreeItem<TreeNodeF> item, PosInOccurrence pio) {
            if (item == null) {
                return null;
            }
            if (item.getValue() != null && Objects.equals(item.getValue().pos(), pio)) {
                return item;
            }
            for (TreeItem<TreeNodeF> child : item.getChildren()) {
                TreeItem<TreeNodeF> found = findTreeItem(child, pio);
                if (found != null) {
                    return found;
                }
            }
            return null;
        }

        /** Detaches nothing (the view has no listeners of its own); kept for symmetry. */
        void dispose() {
            highlightPane.getChildren().clear();
        }

        /** @return whether a non-empty text is printed (self test helper) */
        boolean hasText() {
            return printed != null && !printed.isEmpty();
        }
    }

    /**
     * The printer of the term view (Swing inner class {@code TermViewLogicPrinter extends
     * SequentViewLogicPrinter}): prints the filtered sequent without the arrow when a formula is
     * selected ({@code pos != null}), otherwise the whole sequent like the standard printer.
     */
    private static final class TermViewLogicPrinterF extends SequentViewLogicPrinter {

        private final PosInOccurrence pos;

        TermViewLogicPrinterF(PosInOccurrence pos, NotationInfo ni, Services services) {
            super(ni, services, PosTableLayouter.positionTable(), new TermLabelVisibilityManager());
            this.pos = pos;
        }

        @Override
        public void printFilteredSequent(SequentPrintFilter filter) {
            try {
                ImmutableList<SequentPrintFilterEntry> antec = filter.getFilteredAntec();
                ImmutableList<SequentPrintFilterEntry> succ = filter.getFilteredSucc();
                layouter.markStartSub();
                layouter.startTerm(antec.size() + succ.size());
                layouter.beginC(1).ind();
                printSemisequent(antec);

                if (pos == null) {
                    layouter.brk(1, -1);
                    printSequentArrow();
                    layouter.brk();
                }

                printSemisequent(succ);

                layouter.markEndSub();
                layouter.end();
            } catch (UnbalancedBlocksException e) {
                throw new RuntimeException("Unbalanced blocks in pretty printer:\n" + e);
            }
        }
    }
}
