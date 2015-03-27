package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class HeapGenerator implements TermGenerator {

    public static final TermGenerator INSTANCE = new HeapGenerator();

    private HeapGenerator() {}
    
    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
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
            for (int i = 0; i < term.arity(); i++) {
                collectHeaps(term.sub(i), heaps, services);
            }
        }
    }

}
