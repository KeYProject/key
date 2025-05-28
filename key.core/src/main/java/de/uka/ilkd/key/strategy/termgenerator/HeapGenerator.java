/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

/**
 * The heap generator returns an iterator over all terms of sort heap that
 * <ol>
 * <li>can be found in the sequent</li>
 * <li>are top level in the sense that they are not part of a larger term expression</li>
 * <li>depending on the mode: heaps just occurring in updates are included or ignored</li>
 * </ol>
 */
public class HeapGenerator implements TermGenerator<Goal> {

    public static final TermGenerator<Goal> INSTANCE = new HeapGenerator(true);
    public static final TermGenerator<Goal> INSTANCE_EXCLUDE_UPDATES = new HeapGenerator(false);

    private final boolean includeUpdates;

    private HeapGenerator(boolean includeUpdates) {
        this.includeUpdates = includeUpdates;
    }

    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        LinkedHashSet<Term> heaps = new LinkedHashSet<>();
        Sequent seq = goal.sequent();
        for (SequentFormula sf : seq) {
            collectHeaps(sf.formula(), heaps, goal.proof().getServices());
        }
        return heaps.iterator();
    }

    private void collectHeaps(Term term, LinkedHashSet<Term> heaps, Services services) {
        if (term.sort().equals(services.getTypeConverter().getHeapLDT().targetSort())) {
            heaps.add(term);
        } else {
            if (!includeUpdates && term.op() instanceof UpdateApplication) {
                collectHeaps(UpdateApplication.getTarget((JTerm) term), heaps,
                    services);
            } else {
                for (int i = 0; i < term.arity(); i++) {
                    collectHeaps(term.sub(i), heaps, services);
                }
            }
        }
    }

}
