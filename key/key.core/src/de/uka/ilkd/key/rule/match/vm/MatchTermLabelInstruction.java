package de.uka.ilkd.key.rule.match.vm;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher.TermNavigator;

public class MatchTermLabelInstruction implements IMatchInstruction {

    private final ImmutableArray<TermLabel> labels;

    public MatchTermLabelInstruction(ImmutableArray<TermLabel> labels) {
        this.labels = labels;
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions matchConditions, Services services) {
        final Term term = termPosition.getCurrentSubterm();
        MatchConditions result = matchConditions;
        if (term.getLabels().size() == labels.size()) {
            for (int i = 0; i < labels.size() && result != null; i++) {
                final TermLabel l = labels.get(i);
                // ignore all labels which are not schema variables
                // if intended to match concrete label, match against schema label
                // and use an appropriate variable condition
                if (l instanceof SchemaVariable) {
                    final SchemaVariable schemaLabel = (SchemaVariable) l;
                    result = schemaLabel.match(term, result, services);
                }
            }
        } else {
            result = null;
        }
        return result;
    }

}
