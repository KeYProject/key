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

/**
 * This match instruction implements the matching logic for term labels. 
 */
public class MatchTermLabelInstruction implements MatchInstruction {

    private final ImmutableArray<TermLabel> labels;

    public MatchTermLabelInstruction(ImmutableArray<TermLabel> labels) {
        this.labels = labels;
    }
    
    private MatchConditions match(TermLabelSV sv, Term instantiationCandidate, 
                                  MatchConditions matchCond, Services services) {

        final SVInstantiations svInsts = matchCond.getInstantiations();
        final TermLabelInstantiationEntry inst =
                (TermLabelInstantiationEntry) svInsts.getInstantiation(sv);
        
        if (inst == null) {
            return matchCond.setInstantiations(svInsts.add(sv, instantiationCandidate.getLabels(), services));
        } else {
            for (Object o: (ImmutableArray<?>)inst.getInstantiation()) {
                if (!instantiationCandidate.containsLabel((TermLabel)o)) {
                    return null;
                }
            }
            return matchCond;
        }
    }

    /**
     * {@inheritDoc}
     */
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
