// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Color;
import java.awt.Insets;

import javax.swing.JTextArea;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.MatteBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Highlighter.HighlightPainter;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;

public class InnerNodeView extends SequentView {

    /**
     *
     */
    private static final long serialVersionUID = -6542881446084654358L;
    private InitialPositionTable posTable;
    public final JTextArea tacletInfo;
    Node node;

    public InnerNodeView(Node node, MainWindow mainWindow) {
        super(mainWindow);
        this.node = node;
        filter = new IdentitySequentPrintFilter();
        getFilter().setSequent(node.sequent());
        setLogicPrinter(new SequentViewLogicPrinter(new ProgramPrinter(),
                        mainWindow.getMediator().getNotationInfo(),
                        mainWindow.getMediator().getServices(),
                        getVisibleTermLabels()));
        setSelectionColor(new Color(10, 180, 50));
        setBackground(INACTIVE_BACKGROUND_COLOR);

        tacletInfo = new JTextArea(TacletDescriber.getTacletDescription(mainWindow.getMediator(), node, getFilter()));
        tacletInfo.setBackground(getBackground());
        tacletInfo.setBorder(new CompoundBorder(
                new MatteBorder(3, 0, 0, 0, Color.black),
                new EmptyBorder(new Insets(4, 0, 0, 0))));

//        updateUI();
        printSequent();
    }

    static final HighlightPainter RULEAPP_HIGHLIGHTER
            = new DefaultHighlighter.DefaultHighlightPainter(new Color(0.5f, 1.0f, 0.5f, 0.4f));
    static final HighlightPainter IF_FORMULA_HIGHLIGHTER
            = new DefaultHighlighter.DefaultHighlightPainter(new Color(0.8f, 1.0f, 0.8f, 0.5f));

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
            System.err.println("NonGoalInfoView tried to "
                    + "highlight an area "
                    + "that does not exist.");
            System.err.println("Exception:" + badLocation);
        }
    }

    /**
     * @param tapp The taclet app for which the if formulae should be
     * highlighted.
     * @throws BadLocationException
     */
    private void highlightIfFormulas(TacletApp tapp)
            throws BadLocationException {
        final ImmutableList<IfFormulaInstantiation> ifs = tapp.ifFormulaInstantiations();
        if (ifs == null) {
            return;
        }
        for (final IfFormulaInstantiation inst2 : ifs) {
            if (!(inst2 instanceof IfFormulaInstSeq)) {
                continue;
            }
            final IfFormulaInstSeq inst = (IfFormulaInstSeq) inst2;
            final PosInOccurrence pos
                    = new PosInOccurrence(inst.getConstrainedFormula(),
                    PosInTerm.getTopLevel(),
                    inst.inAntec());
            highlightPos(pos, IF_FORMULA_HIGHLIGHTER);
        }
    }

    private void highlightIfInsts(IBuiltInRuleApp bapp)
            throws BadLocationException {
        final ImmutableList<PosInOccurrence> ifs = bapp.ifInsts();
        for (PosInOccurrence pio : ifs) {
            highlightPos(pio, IF_FORMULA_HIGHLIGHTER);
        }
    }

    /**
     * @param pos the PosInOccurrence that should be highlighted.
     * @param light the painter for the highlight.
     * @return the range of characters that was highlighted. returns null if nothing has been highlighted.
     * @throws BadLocationException
     */
    private Range highlightPos(PosInOccurrence pos,
            HighlightPainter light)
            throws BadLocationException {
        ImmutableList<Integer> path = posTable.pathForPosition(pos, getFilter());
        if(path != null) {
            Range r = posTable.rangeForPath(path);

            // NOTE (DS): The below addition of 1 to the beginning is a quick-and-dirty
            // fix for a shift of highlighted areas to the left that occurred after the
            // change to HTML documents in the JEditorPane (previous JTextArea). If
            // something concerning highlighting does not work in the future, here could
            // be a starting place to find the mistake.
            getHighlighter().addHighlight(r.start() + 1, r.end() + 1, light);
            return r;
        } else {
            return null;
        }
        
    }

    @Override
    public String getTitle() {
        return "Inner Node";
    }

    @Override
    public final synchronized void printSequent() {
        setLineWidth(computeLineWidth());
        getLogicPrinter().update(getFilter(), getLineWidth());
        setText(getSyntaxHighlighter().process(getLogicPrinter().toString(), node));
        posTable = getLogicPrinter().getInitialPositionTable();
        RuleApp app = node.getAppliedRuleApp();
        
        if (app != null) {
            highlightRuleAppPosition(app);
        }

        updateHidingProperty();
        updateHeatMapHighlights();
    }

}