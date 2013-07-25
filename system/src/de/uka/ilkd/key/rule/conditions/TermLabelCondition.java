package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TermLabelCondition extends VariableConditionAdapter {

    private final TermLabelSV l;
    private final Name ln;
    private final boolean negated;

    public TermLabelCondition(TermLabelSV l, String t, boolean negated) {
        this.l = l;
        this.ln = makeLabelName(t);
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
                         SVInstantiations instMap, Services services) {
        assert instMap.getInstantiation(l) instanceof ImmutableArray<?>;
        ImmutableArray<?> tInsts = (ImmutableArray<?>) instMap.getInstantiation(l);
        boolean isLabel = hasLabel(tInsts, ln);
        return negated ? !isLabel : isLabel;
    }

    static boolean hasLabel(ImmutableArray<?> labels, Name name) {
        boolean found = false;
        for (Object o: labels) {
            assert o instanceof ITermLabel;
            ITermLabel label = (ITermLabel)o;
            found = found || (label.name().compareTo(name) == 0);
        }
        return found;
    }

    static Name makeLabelName(String name) {
        for (ITermLabel l: ITermLabel.labels) {
            if(l.toString().equalsIgnoreCase(name)) {
                return l.name();
            }
        }
        assert false : "Unknown Term Label!";
        return null;
    }

    @Override
    public String toString() {
        return (negated ? "\\not":"") + "\\isLabel (" + l + ", " + ln + ")";
    }
}