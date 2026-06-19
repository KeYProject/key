/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.pp.InitialPositionTable;
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
 * displays
 * the logical content (find/matched/bindings/preview), where origin and other labels are noise.
 */
final class TmPrint {

    /** a label visibility that hides every term label */
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

    private TmPrint() {}

    static String term(KeYMediator mediator, Term t) {
        SequentViewLogicPrinter p = printer(mediator);
        p.printTerm((JTerm) t);
        return p.result();
    }

    /** a printed term together with the position table that maps its sub-terms to char ranges. */
    record Positioned(String text, InitialPositionTable positions) {
    }

    /**
     * like {@link #term} but also returns the position table, so callers can highlight individual
     * sub-terms (e.g. the parts a schema variable matched) inside the printed term.
     */
    static Positioned termWithPositions(KeYMediator mediator, Term t) {
        Services services = mediator.getServices();
        NotationInfo ni = new NotationInfo();
        SequentViewLogicPrinter p =
            SequentViewLogicPrinter.positionPrinter(ni, services, NO_LABELS);
        ni.refresh(services, mediator.getNotationInfo().isPrettySyntax(), false, false);
        // wrap the term in a sub so it is linked under the position table's root row [0]
        // (printSequent does this for each formula; a bare printTerm does not)
        p.layouter().markStartSub();
        p.printTerm((JTerm) t);
        p.layouter().markEndSub();
        return new Positioned(p.result(), p.layouter().getInitialPositionTable());
    }

    static String taclet(KeYMediator mediator, Taclet taclet) {
        SequentViewLogicPrinter p = printer(mediator);
        p.printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getShowWholeTaclet(),
            false);
        return p.result();
    }

    /** prints a schema-variable instantiation (a term, program element, ...) without labels. */
    static String instantiation(KeYMediator mediator, Object value) {
        Object o = value instanceof InstantiationEntry<?> e ? e.getInstantiation() : value;
        if (o instanceof Term t) {
            return term(mediator, t);
        }
        return ProofSaver.printAnything(o, mediator.getServices());
    }

    private static SequentViewLogicPrinter printer(KeYMediator mediator) {
        Services services = mediator.getServices();
        NotationInfo ni = new NotationInfo();
        SequentViewLogicPrinter p = SequentViewLogicPrinter.purePrinter(ni, services, NO_LABELS);
        ni.refresh(services, mediator.getNotationInfo().isPrettySyntax(), false, false);
        return p;
    }
}
