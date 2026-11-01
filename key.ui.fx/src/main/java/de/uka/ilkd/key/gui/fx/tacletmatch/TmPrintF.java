/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.Notation;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.prover.rules.instantiation.InstantiationEntry;

/**
 * Pretty-printing for the taclet-match dialog. Term labels are never shown here: the dialog
 * displays the logical content (find/matched/bindings/preview), where origin and other labels are
 * noise.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.TmPrint} (TmPrint.java:29-98). The Swing helper
 * takes the {@code KeYMediator} to obtain the services and the shared notation info; the FX port
 * takes both directly, so the dialog compiles against the core proof control without the
 * Swing-style mediator (the FX mediator passes its shared {@link NotationInfo}).
 */
public final class TmPrintF {

    /** a label visibility that hides every term label (TmPrint.java:32-42) */
    private static final VisibleTermLabels NO_LABELS = new VisibleTermLabels() {
        @Override
        public boolean contains(TermLabel label) {
            return false;
        }

        @Override
        public boolean contains(Name name) {
            return false;
        }
    };

    private TmPrintF() {}

    public static String term(Services services, NotationInfo notationInfo, Term t) {
        SequentViewLogicPrinter p = printer(services, notationInfo);
        p.printTerm((JTerm) t);
        return p.result();
    }

    /** a printed term together with the position table that maps its sub-terms to char ranges */
    record Positioned(String text, InitialPositionTable positions) {
    }

    /**
     * like {@link #term} but also returns the position table, so callers can highlight individual
     * sub-terms (e.g. the parts a schema variable matched) inside the printed term
     * (TmPrint.java:60-72).
     */
    static Positioned termWithPositions(Services services, NotationInfo notationInfo, Term t) {
        NotationInfo ni = new NotationInfo();
        SequentViewLogicPrinter p =
            SequentViewLogicPrinter.positionPrinter(ni, services, NO_LABELS);
        ni.refresh(services, notationInfo.isPrettySyntax(), false, false);
        // wrap the term in a sub so it is linked under the position table's root row [0]
        // (printSequent does this for each formula; a bare printTerm does not)
        p.layouter().markStartSub();
        p.printTerm((JTerm) t);
        p.layouter().markEndSub();
        return new Positioned(p.result(), p.layouter().getInitialPositionTable());
    }

    public static String taclet(Services services, NotationInfo notationInfo, Taclet taclet) {
        SequentViewLogicPrinter p = printer(services, notationInfo);
        p.printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getShowWholeTaclet(),
            false);
        return p.result();
    }

    /** prints a schema-variable instantiation (a term, program element, ...) without labels */
    public static String instantiation(Services services, NotationInfo notationInfo, Object value) {
        Object o = value instanceof InstantiationEntry<?> e ? e.getInstantiation() : value;
        if (o instanceof Term t) {
            return term(services, notationInfo, t);
        }
        return ProofSaver.printAnything(o, services);
    }

    /**
     * prints a term for insertion into an instantiation field. A few notations the parser cannot
     * yet round-trip are disabled, mirroring the classic dialog, so the result re-parses
     * (SVInstantiationPanel.java:426-448, TacletMatchCompletionDialog.java:709-736).
     */
    static String printTermForInstantiation(Services services, NotationInfo sharedNotationInfo,
            JTerm term) {
        final NotationInfo ni = new NotationInfo();
        final JTerm t = TermLabelManager.removeIrrelevantLabels(term, services);
        LogicPrinter p = LogicPrinter.purePrinter(ni, services);
        boolean pretty = sharedNotationInfo.isPrettySyntax();
        ni.refresh(services, pretty, false, false);
        Map<Object, Notation> tbl = ni.getNotationTable();

        if (pretty) {
            final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
            tbl.remove(setLDT.getUnion());
            tbl.remove(setLDT.getIntersect());
            tbl.remove(setLDT.getSetMinus());
            tbl.remove(setLDT.getElementOf());
            tbl.remove(setLDT.getSubset());
            tbl.remove(IObserverFunction.class);
            tbl.remove(IProgramMethod.class);
        }

        p.printTerm(t);
        return p.result();
    }

    private static SequentViewLogicPrinter printer(Services services,
            NotationInfo notationInfo) {
        NotationInfo ni = new NotationInfo();
        SequentViewLogicPrinter p = SequentViewLogicPrinter.purePrinter(ni, services, NO_LABELS);
        ni.refresh(services, notationInfo.isPrettySyntax(), false, false);
        return p;
    }
}
