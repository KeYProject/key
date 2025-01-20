/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;

/**
 * This class completes the instantiation for a dependency contract applications. The user is
 * queried for the heap with which to instantiate the app.
 */
public class DependencyContractCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        UseDependencyContractApp cApp = (UseDependencyContractApp) app;

        Services services = goal.proof().getServices();

        cApp = cApp.tryToInstantiateContract(services);

        final List<PosInOccurrence> steps = UseDependencyContractRule
                .getSteps(cApp.getHeapContext(), cApp.posInOccurrence(), goal.sequent(), services);
        PosInOccurrence step = letUserChooseStep(cApp.getHeapContext(), steps, forced, services);
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
    private static PosInOccurrence letUserChooseStep(List<LocationVariable> heapContext,
            List<PosInOccurrence> steps, boolean forced, Services services) {
        assert heapContext != null;

        if (steps.size() == 0) {
            return null;
        }

        // prepare array of possible base heaps
        final TermStringWrapper[] heaps = new TermStringWrapper[steps.size()];
        final LogicPrinter lp =
            new LogicPrinter(new NotationInfo(), services, PosTableLayouter.pure(120));

        extractHeaps(heapContext, steps, heaps, lp);

        final Term[] resultHeaps;
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

    public static PosInOccurrence findCorrespondingStep(List<PosInOccurrence> steps,
            Term[] resultHeaps) {
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

    public static void extractHeaps(List<LocationVariable> heapContext, List<PosInOccurrence> steps,
            final TermStringWrapper[] heaps, final LogicPrinter lp) {
        int i = 0;
        for (PosInOccurrence step : steps) {
            Operator op = step.subTerm().op();
            // necessary distinction (see bug #1232)
            // subterm may either be an observer or a heap term already
            int size = (op instanceof IObserverFunction)
                    ? ((IObserverFunction) op).getStateCount() * heapContext.size()
                    : 1;
            final Term[] heapTerms = new Term[size];
            StringBuilder prettyPrint = new StringBuilder("<html><tt>").append(size > 1 ? "[" : "");
            for (int j = 0; j < size; j++) {
                // TODO: there may still be work to do
                // what if we have a heap term, where the base heap lies deeper?
                final Term heap = step.subTerm().sub(j);
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
        public final Term[] terms;
        final String string;

        public TermStringWrapper(Term[] terms, String string) {
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
