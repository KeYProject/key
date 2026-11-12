/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.contractcompletions;

import java.util.List;
import javafx.scene.control.ChoiceDialog;

import de.uka.ilkd.key.gui.fx.InteractiveRuleApplicationCompletionF;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;

import org.key_project.prover.sequent.PosInOccurrence;

/**
 * contractcompletions (P2b): JavaFX port of the Swing {@code DependencyContractCompletion}
 * (DependencyContractCompletion.java, 168 lines) — the interactive completion of a use
 * dependency contract application: the user chooses the base heap configuration (one of the
 * observer's state steps) via a dialog.
 * <p>
 * Deviation: the Swing heap chooser is a {@code JOptionPane.showInputDialog} whose options carry
 * {@code <html><tt>} styled strings; the FX port shows a {@link ChoiceDialog} with plain-text
 * heap strings (the HTML escaping is dropped, see KNOWN-SIMPLIFIED).
 */
public class DependencyContractCompletionF implements InteractiveRuleApplicationCompletionF {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        UseDependencyContractApp cApp = (UseDependencyContractApp) app;

        Services services = goal.proof().getServices();

        cApp = cApp.tryToInstantiateContract(services);

        final List<PosInOccurrence> steps = UseDependencyContractRule
                .getSteps(cApp.getHeapContext(), cApp.posInOccurrence(), goal.sequent(), services);
        PosInOccurrence step =
            letUserChooseStep(cApp.getHeapContext(), steps, forced, services);
        if (step == null) {
            return null;
        }
        return cApp.setStep(step);
    }

    /** Swing {@code letUserChooseStep} (DependencyContractCompletion.java:61-98). */
    private static PosInOccurrence letUserChooseStep(List<LocationVariable> heapContext,
            List<PosInOccurrence> steps, boolean forced, Services services) {
        assert heapContext != null;

        if (steps.isEmpty()) {
            return null;
        }

        // prepare array of possible base heaps
        final TermStringWrapper[] heaps = new TermStringWrapper[steps.size()];
        final LogicPrinter lp =
            new LogicPrinter(new NotationInfo(), services, PosTableLayouter.pure(120));

        extractHeaps(heapContext, steps, heaps, lp);

        final JTerm[] resultHeaps;
        if (!forced) {
            // open dialog (Swing JOptionPane.showInputDialog with the heap options)
            ChoiceDialog<TermStringWrapper> dialog = new ChoiceDialog<>(heaps[0], heaps);
            dialog.setTitle("Instantiation");
            dialog.setHeaderText("Please select base heap configuration:");
            dialog.showAndWait();
            TermStringWrapper heapWrapper = dialog.getResult();
            if (heapWrapper == null) {
                return null;
            }
            resultHeaps = heapWrapper.terms;
        } else {
            resultHeaps = heaps[0].terms;
        }

        return findCorrespondingStep(steps, resultHeaps);
    }

    /** Swing {@code findCorrespondingStep} (DependencyContractCompletion.java:101-114). */
    public static PosInOccurrence findCorrespondingStep(List<PosInOccurrence> steps,
            JTerm[] resultHeaps) {
        // find corresponding step
        for (PosInOccurrence step : steps) {
            boolean match = true;
            for (int j = 0; j < resultHeaps.length; j++) {
                if (!step.subTerm().sub(j).equals(resultHeaps[j])) {
                    match = false;
                    break;
                }
            }
            if (match) {
                return step;
            }
        }
        assert false;
        return null;
    }

    /**
     * Swing {@code extractHeaps} (DependencyContractCompletion.java:117-137): prints the heap
     * terms of every step; the display string is the plain printed text (Swing escapes it into
     * a {@code <html><tt>} wrapper — dropped in the FX port, see the class javadoc).
     */
    public static void extractHeaps(List<LocationVariable> heapContext,
            List<PosInOccurrence> steps, TermStringWrapper[] heaps, LogicPrinter lp) {
        int i = 0;
        for (PosInOccurrence step : steps) {
            var op = step.subTerm().op();
            // necessary distinction (see bug #1232)
            // subterm may either be an observer or a heap term already
            int size =
                (op instanceof IObserverFunction iof) ? iof.getStateCount() * heapContext.size()
                        : 1;
            final JTerm[] heapTerms = new JTerm[size];
            StringBuilder prettyPrint = new StringBuilder(size > 1 ? "[" : "");
            for (int j = 0; j < size; j++) {
                final JTerm heap = (JTerm) step.subTerm().sub(j);
                heapTerms[j] = heap;
                lp.reset();
                lp.printTerm(heap);
                prettyPrint.append(j > 0 ? ", " : "").append(lp.result().trim());
            }
            prettyPrint.append(size > 1 ? "]" : "");
            heaps[i++] = new TermStringWrapper(heapTerms, prettyPrint.toString());
        }
    }

    /** Swing nested class {@code TermStringWrapper}. */
    public static final class TermStringWrapper {
        public final JTerm[] terms;
        final String string;

        public TermStringWrapper(JTerm[] terms, String string) {
            this.terms = terms;
            this.string = string;
        }

        @Override
        public String toString() {
            return string;
        }
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }

    /** Swing {@code checkCanComplete} (also used by the KeY IDE). */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
        return app.rule() instanceof UseDependencyContractRule;
    }
}
