/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.*;
import java.awt.geom.Rectangle2D;
import javax.swing.*;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.MatteBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Highlighter.HighlightPainter;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.smt.SMTRuleApp;

import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Sequent view for an inner node.
 */
public final class InnerNodeView extends SequentView implements ProofDisposedListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(InnerNodeView.class);

    private static final ColorSettings.ColorProperty RULE_APP_HIGHLIGHT_COLOR = ColorSettings
            .define("[innerNodeView]ruleAppHighlight", "", new Color(0.5f, 1.0f, 0.5f, 0.4f));

    private static final ColorSettings.ColorProperty IF_FORMULA_HIGHLIGHT_COLOR = ColorSettings
            .define("[innerNodeView]ifFormulaHighlight", "", new Color(0.8f, 1.0f, 0.8f, 0.5f));

    private static final ColorSettings.ColorProperty SELECTION_COLOR =
        ColorSettings.define("[innerNodeView]selection", "", new Color(10, 180, 50));

    private static final long serialVersionUID = -6542881446084654358L;


    private InitialPositionTable posTable;

    private final InnerNodeViewListener listener;

    public final JTextArea tacletInfo;

    private Node node;
    private final RuleApp ruleApp;

    public InnerNodeView(Node node, MainWindow mainWindow) {
        this(node.proof(), node, node.getAppliedRuleApp(), node.sequent(), mainWindow);
    }

    public InnerNodeView(Proof proof, Node node, RuleApp ruleApp, Sequent sequent,
            MainWindow mainWindow) {
        super(mainWindow);
        this.node = node;
        this.ruleApp = ruleApp;
        proof.addProofDisposedListener(this);
        this.listener = new InnerNodeViewListener(this);

        filter = new IdentitySequentPrintFilter();
        getFilter().setSequent(sequent);
        setLogicPrinter(
            SequentViewLogicPrinter.positionPrinter(mainWindow.getMediator().getNotationInfo(),
                mainWindow.getMediator().getServices(), getVisibleTermLabels()));
        setSelectionColor(SELECTION_COLOR.get());
        setBackground(INACTIVE_BACKGROUND_COLOR);

        tacletInfo = new JTextArea(
            TacletDescriber.getTacletDescription(mainWindow.getMediator(), ruleApp,
                SequentView.getLineWidth()));
        tacletInfo.setBackground(getBackground());
        tacletInfo.setBorder(new CompoundBorder(new MatteBorder(3, 0, 0, 0, Color.black),
            new EmptyBorder(new Insets(4, 0, 0, 0))));
        tacletInfo.setEditable(false);
    }

    static final HighlightPainter RULEAPP_HIGHLIGHTER =
        new DefaultHighlighter.DefaultHighlightPainter(RULE_APP_HIGHLIGHT_COLOR.get());

    static final HighlightPainter IF_FORMULA_HIGHLIGHTER =
        new DefaultHighlighter.DefaultHighlightPainter(IF_FORMULA_HIGHLIGHT_COLOR.get());

    private void highlightRuleAppPosition(RuleApp app) {
        try {
            // Set the find highlight first and then the if highlights
            // This seems to make cause the find one to be painted
            // over the if one.

            if (app.posInOccurrence() != null) {
                highlightPos(app.posInOccurrence(), RULEAPP_HIGHLIGHTER);
            }

            if (app instanceof TacletApp) {
                highlightIfFormulas((TacletApp) app);
            } else if (app instanceof IBuiltInRuleApp) {
                highlightIfInsts((IBuiltInRuleApp) app);
            }

        } catch (BadLocationException badLocation) {
            LOGGER.warn("NonGoalInfoView tried to highlight an area that does not exist.",
                badLocation);
        }
    }

    /**
     * @param tapp The taclet app for which the if formulae should be highlighted.
     * @throws BadLocationException
     */
    private void highlightIfFormulas(TacletApp tapp) throws BadLocationException {
        final ImmutableList<IfFormulaInstantiation> ifs = tapp.ifFormulaInstantiations();
        if (ifs == null) {
            return;
        }
        for (final IfFormulaInstantiation inst2 : ifs) {
            if (!(inst2 instanceof IfFormulaInstSeq)) {
                continue;
            }
            final IfFormulaInstSeq inst = (IfFormulaInstSeq) inst2;
            final PosInOccurrence pos = new PosInOccurrence(inst.getConstrainedFormula(),
                PosInTerm.getTopLevel(), inst.inAntec());
            highlightPos(pos, IF_FORMULA_HIGHLIGHTER);
        }
    }

    private void highlightIfInsts(IBuiltInRuleApp bapp) throws BadLocationException {
        final ImmutableList<PosInOccurrence> ifs = bapp.ifInsts();
        if (bapp instanceof SMTRuleApp && ifs.isEmpty()) {
            /*
             * Special case for SMTRuleApp: If no unsat core is used, we highlight all formulas.
             * For the moment, we do not store all formulas as ifInstantiations, since that would
             * clutter saved proofs very much.
             */
            for (int i = 0; i < node.sequent().size(); i++) {
                PosInOccurrence pio = PosInOccurrence.findInSequent(node.sequent(), i + 1,
                    PosInTerm.getTopLevel());
                highlightPos(pio, IF_FORMULA_HIGHLIGHTER);
            }
        } else {
            for (PosInOccurrence pio : ifs) {
                highlightPos(pio, IF_FORMULA_HIGHLIGHTER);
            }
        }
    }

    /**
     * @param pos the PosInOccurrence that should be highlighted.
     * @param light the painter for the highlight.
     * @return the range of characters that was highlighted. returns null if nothing has been
     *         highlighted.
     * @throws BadLocationException
     */
    private Range highlightPos(PosInOccurrence pos, HighlightPainter light)
            throws BadLocationException {
        ImmutableList<Integer> path = posTable.pathForPosition(pos, getFilter());
        if (path != null) {
            Range r = posTable.rangeForPath(path);

            // NOTE (DS): The below addition of 1 to the beginning is a quick-and-dirty
            // fix for a shift of highlighted areas to the left that occurred after the
            // change to HTML documents in the JEditorPane (previous JTextArea). If
            // something concerning highlighting does not work in the future, here could
            // be a starting place to find the mistake.
            getHighlighter().addHighlight(r.start() + 1, r.end() + 1, light);

            // scroll the active formula into view
            SwingUtilities.invokeLater(() -> {
                try {
                    ImmutableList<Integer> pathTop =
                        posTable.pathForPosition(pos.topLevel(), getFilter());
                    if (pathTop == null) {
                        return;
                    }
                    Range rFormula = posTable.rangeForPath(pathTop);
                    Rectangle2D rect = modelToView2D(rFormula.start() + 1);
                    Rectangle2D rectTerm = modelToView2D(r.start() + 1);

                    Rectangle visible = getVisibleRect();
                    if (rect != null && visible != null
                            && !visible.contains(rectTerm.getMinX(), rectTerm.getMinY())) {
                        // scroll into view: first check if the sub-term is visible if we would
                        // scroll to the top of the sequent formula
                        if (rectTerm.getMinY() - rect.getMinY() > visible.getHeight()) {
                            // it isn't: center the sub-term in view
                            int y = (int) (rectTerm.getMinY() - visible.getHeight() / 2.0);
                            MainWindow.getInstance().scrollTo(y);
                        } else {
                            // it is: scroll to the sequent formula
                            MainWindow.getInstance().scrollTo((int) rect.getMinY());
                        }
                    }
                } catch (BadLocationException e) {
                    LOGGER.warn("could not scroll active formula into view ", e);
                }
            });

            return r;
        } else {
            return null;
        }

    }

    @Override
    public String getTitle() {
        // If a leaf becomes an inner node, it is already closed.
        if (node != null && node.leaf()) {
            return "Closed Goal";
        }
        return "Inner Node";
    }

    @Override
    public synchronized void printSequent() {
        var time = System.nanoTime();
        getHighlighter().removeAllHighlights();
        removeMouseListener(listener);

        setLineWidth(computeLineWidth());
        updateSequent(node);
        posTable = getInitialPositionTable();

        if (ruleApp != null) {
            highlightRuleAppPosition(ruleApp);
        }

        updateHidingProperty();
        updateHeatMapHighlights();

        addMouseListener(listener);
        var after = System.nanoTime();
        LOGGER.debug("Total printSequent took " + (after - time) / 1e6 + "ms");
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        node = null;
        dispose();
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {

    }
}
