package de.uka.ilkd.key.rule.match.vm.instructions;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.TermLabelInstantiationEntry;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchTermLabelInstruction implements IMatchInstruction {

    private final ImmutableArray<TermLabel> labels;

    public MatchTermLabelInstruction(ImmutableArray<TermLabel> labels) {
        this.labels = labels;
    }
    
    private MatchConditions match(TermLabelSV sv, Term instantiationCandidate, 
                                  MatchConditions matchCond, Services services) {

        final SVInstantiations svInsts = matchCond.getInstantiations();
        final TermLabelInstantiationEntry inst =
                (TermLabelInstantiationEntry) svInsts.getInstantiation(sv);
        
        final MatchConditions result;
        if (inst == null) {
            result = matchCond.setInstantiations(svInsts.add(sv, instantiationCandidate.getLabels(), services));
        } else {
            boolean matched = false;
            for (Object o: (ImmutableArray<?>)inst.getInstantiation()) {
                matched = instantiationCandidate.containsLabel((TermLabel)o);
                if (!matched) {
                    return null;
                }
            }
            if (matched) {
                result = matchCond;
            } else {
                result = null;
            }
        }
        return result;
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions matchConditions, Services services) {
        final Term term = termPosition.getCurrentSubterm();
        MatchConditions result = matchConditions;
        if (term.getLabels().size() == labels.size()) {
            for (int i = 0; i < labels.size() && result != null; i++) {
                final TermLabel templateLabel = labels.get(i);
                // ignore all labels which are not schema variables
                // if intended to match concrete label, match against schema label
                // and use an appropriate variable condition
                if (templateLabel instanceof TermLabelSV) {
                    result = match((TermLabelSV) templateLabel, term, result, services);
                }
            }
        } else {
            result = null;
        }
        return result;
    }

}
