/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import java.util.Objects;
import java.util.function.Consumer;
import javafx.geometry.Insets;
import javafx.geometry.Point2D;
import javafx.scene.control.ScrollPane;
import javafx.scene.input.MouseEvent;
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
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;
import org.key_project.util.javafx.FxUtil;

/**
 * First JavaFX version of the sequent view, the counter-part of
 * {@code de.uka.ilkd.key.gui.nodeviews.SequentView} (a Swing {@code JEditorPane} with HTML
 * content) in the module {@code key.ui}.
 * <p>
 * <b>Milestone M2a spike.</b> The rendering pipeline reuses the UI-agnostic pretty-printer of
 * {@code key.core}: {@link SequentViewLogicPrinter} produces the printed sequent string together
 * with an {@link InitialPositionTable} that maps character indexes to {@link PosInSequent}s.
 * The string is rendered as {@link Text} runs inside a {@link TextFlow}; mouse clicks are mapped
 * with {@link TextFlow#getHitInfo} back to a character index and hence to a {@link PosInSequent}
 * -- no HTML, no AWT.
 * <p>
 * The spike intentionally supports only a plain character-grid rendering (monospaced font like
 * the Swing view) and click highlighting; syntax highlighting, hover tooltips, update
 * highlighting, sequent hiding and mediator wiring arrive with the milestone M2 implementation.
 */
public class SequentViewF extends ScrollPane {

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

    private final TextFlow textFlow = new TextFlow();

    private final IdentitySequentPrintFilter filter = new IdentitySequentPrintFilter();

    private SequentViewLogicPrinter printer;
    private Proof proof;
    private Node selectedNode;
    private String printed;
    private Range highlightedRange;

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
        setFitToWidth(true);
        setFitToHeight(true);
        setContent(textFlow);
        textFlow.getStyleClass().add("sequent-view-flow");
        textFlow.setPadding(new Insets(6));
        textFlow.setOnMouseClicked(this::handleMouseClick);
        printPlaceholder();
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

    private void rebuildRuns() {
        textFlow.getChildren().clear();
        if (printed == null) {
            return;
        }
        Font font = ConfigF.DEFAULT.monoFont();
        if (highlightedRange == null) {
            addRun(printed, font, "sequent-text");
            return;
        }
        int start = Math.clamp(highlightedRange.start(), 0, printed.length());
        int end = Math.clamp(highlightedRange.end(), start, printed.length());
        addRun(printed.substring(0, start), font, "sequent-text");
        addRun(printed.substring(start, end), font, "sequent-text", "sequent-term-highlight");
        addRun(printed.substring(end), font, "sequent-text");
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
