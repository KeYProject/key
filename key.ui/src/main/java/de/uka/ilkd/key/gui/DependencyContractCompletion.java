/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.util.List;
import javax.swing.*;

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

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class completes the instantiation for a dependency contract applications. The user is
 * queried for the heap with which to instantiate the app.
 */
@NullMarked
public class DependencyContractCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public @Nullable IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        UseDependencyContractApp cApp = (UseDependencyContractApp) app;

        Services services = goal.proof().getServices();

        cApp = cApp.tryToInstantiateContract(services);

        List<LocationVariable> heapContext = cApp.getHeapContext();
        if (heapContext == null) {
            // the rule always resolves a heap context for instantiated contract apps
            throw new NullPointerException("No heap context available.");
        }
        PosInOccurrence posInOccurrence = cApp.posInOccurrence();
        if (posInOccurrence == null) {
            // an operation-contract rule app always carries a position
            throw new NullPointerException("No position in occurrence available.");
        }

        final List<PosInOccurrence> steps = UseDependencyContractRule.getSteps(heapContext,
            posInOccurrence, goal.sequent(), services);
        PosInOccurrence step =
            letUserChooseStep(heapContext, steps, forced, services);
        if (step == null) {
            return null;
        }
        return cApp.setStep(step);
    }

    /**
     * collects all possible heaps and presents them to the user for selection. If forced is true
     * the user will not be asked if only one alternative is possible
     *
     * @param steps
     * @param forced
     * @param services
     * @return
     */
    private static @Nullable PosInOccurrence letUserChooseStep(
            List<LocationVariable> heapContext,
            List<PosInOccurrence> steps, boolean forced,
            Services services) {
        assert heapContext != null;

        if (steps.size() == 0) {
            return null;
        }

        // prepare array of possible base heaps
        final TermStringWrapper[] heaps = new TermStringWrapper[steps.size()];
        final LogicPrinter lp =
            new LogicPrinter(new NotationInfo(), services, PosTableLayouter.pure(120));

        extractHeaps(heapContext, steps, heaps, lp);

        final JTerm[] resultHeaps;
        if (!forced) {
            // open dialog
            final TermStringWrapper heapWrapper =
                (TermStringWrapper) JOptionPane.showInputDialog(MainWindow.getInstance(),
                    "Please select base heap configuration:", "Instantiation",
                    JOptionPane.QUESTION_MESSAGE, null, heaps, heaps[0]);

            if (heapWrapper == null) {
                return null;
            }
            resultHeaps = heapWrapper.terms;
        } else {
            resultHeaps = heaps[0].terms;
        }

        return findCorrespondingStep(steps, resultHeaps);
    }

    public static @Nullable PosInOccurrence findCorrespondingStep(
            List<PosInOccurrence> steps,
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

    public static void extractHeaps(List<LocationVariable> heapContext,
            List<PosInOccurrence> steps,
            final TermStringWrapper[] heaps, final LogicPrinter lp) {
        int i = 0;
        for (PosInOccurrence step : steps) {
            var op = step.subTerm().op();
            // necessary distinction (see bug #1232)
            // subterm may either be an observer or a heap term already
            int size = (op instanceof IObserverFunction iof)
                    ? iof.getStateCount() * heapContext.size()
                    : 1;
            final JTerm[] heapTerms = new JTerm[size];
            StringBuilder prettyPrint = new StringBuilder("<html><tt>").append(size > 1 ? "[" : "");
            for (int j = 0; j < size; j++) {
                // TODO: there may still be work to do
                // what if we have a heap term, where the base heap lies deeper?
                final JTerm heap = (JTerm) step.subTerm().sub(j);
                heapTerms[j] = heap;
                lp.reset();
                lp.printTerm(heap);
                prettyPrint.append(j > 0 ? ", " : "")
                        .append(LogicPrinter.escapeHTML(lp.result().trim(), true));
            }
            prettyPrint.append(size > 1 ? "]" : "").append("</tt></html>");
            heaps[i++] = new TermStringWrapper(heapTerms, prettyPrint.toString());
        }
    }

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

    /**
     * Checks if the app is supported. This functionality is also used by the Eclipse plug-ins like
     * the KeYIDE.
     */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
        return app.rule() instanceof UseDependencyContractRule;
    }
}
