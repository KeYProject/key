package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.TermLabelInstantiationEntry;

/**
 * A schema variable which matches term labels
 */
public final class TermLabelSV extends AbstractSV implements SchemaVariable, ITermLabel {

    protected TermLabelSV(Name name) {
        super(name, Sort.TERMLABEL, true, false);
    }

    @Override
    public String proofToString() {
        return "\\schemaVar \\termlabel " + name() + ";\n";
    }

    @Override
    public String toString() {
        return toString("termLabel");
    }

    @Override
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
                                 Services services) {
        if (!(subst instanceof Term)) {
            return null;
        }

        final Term t = (Term)subst;
        if (!t.hasLabels()) {
            return null;
        }
        final SVInstantiations svInsts = mc.getInstantiations();
        final TermLabelInstantiationEntry inst =
                (TermLabelInstantiationEntry) svInsts.getInstantiation(this);
        if (inst != null) {
            if (t.getLabels().equals(inst.getInstantiation())) {
                return mc;
            }
            return null;
        }
        return mc.setInstantiations(svInsts.add(this, t.getLabels(), services));
    }

    @Override
    public boolean validTopLevel(Term term) {
        return true;
    }

    @Override
    public Object getChild(int i) {
        throw new IndexOutOfBoundsException();
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}