// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import java.io.IOException;
import java.util.List;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;

/**
 * This class completes the instantiation for a dependency contract
 * applications. The user is queried for the heap with which to instantiate the
 * app.
 */
public class DependencyContractCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal,
            boolean forced) {
        UseDependencyContractApp cApp = (UseDependencyContractApp) app;

        Services services = goal.proof().getServices();

        cApp = cApp.tryToInstantiateContract(services);

        final List<PosInOccurrence> steps = UseDependencyContractRule.getSteps(
                cApp.posInOccurrence(), goal.sequent(), services);
        PosInOccurrence step = letUserChooseStep(steps, forced, services);
        if (step == null) {
            return null;
        }
        return cApp.setStep(step);
    }

    /**
     * collects all possible heaps and presents them to the user for selection.
     * If forced is true the user will not be asked if only one alternative is possible
     * @param steps 
     * @param forced
     * @param services
     * @return
     */
    private static PosInOccurrence letUserChooseStep(
            List<PosInOccurrence> steps, boolean forced, Services services) {

        if (steps.size() == 0) {
            return null;
        }

        // prepare array of possible base heaps
        final TermStringWrapper[] heaps = new TermStringWrapper[steps.size()];
        int i = 0;
        final LogicPrinter lp = new LogicPrinter(null, new NotationInfo(),
                services);
        lp.setLineWidth(120);

        for (PosInOccurrence step : steps) {
            final Term heap = step.subTerm().sub(0);
            lp.reset();
            try {
                lp.printTerm(heap);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
            String prettyprint = lp.toString();
            prettyprint = "<html><tt>"
                    + LogicPrinter.escapeHTML(prettyprint, true)
                    + "</tt></html>";
            heaps[i++] = new TermStringWrapper(heap, prettyprint);
        }

        final Term heap;
        if (!forced) {
            // open dialog
            final TermStringWrapper heapWrapper = (TermStringWrapper) JOptionPane
                    .showInputDialog(MainWindow.getInstance(),
                            "Please select a base heap:", "Instantiation",
                            JOptionPane.QUESTION_MESSAGE, null, heaps,
                            heaps.length > 0 ? heaps[0] : null);

            if (heapWrapper == null) {
                return null;
            }
            heap = heapWrapper.term;
        } else {
            heap = heaps[0].term;
        }

        // find corresponding step
        for (PosInOccurrence step : steps) {
            if (step.subTerm().sub(0).equals(heap)) {
                return step;
            }
        }

        assert false;
        return null;
    }

    private static final class TermStringWrapper {
        final Term term;
        final String string;

        TermStringWrapper(Term term, String string) {
            this.term = term;
            this.string = string;
        }

        @Override
        public String toString() {
            return string;
        }
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return app.rule() instanceof UseDependencyContractRule;
    }
}