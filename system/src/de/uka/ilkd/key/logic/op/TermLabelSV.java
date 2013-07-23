package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
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
public class TermLabelSV implements SchemaVariable, ITermLabel {

    private final Name name;

    protected TermLabelSV(Name name) {
        this.name = name;
    }

    @Override
    public String proofToString() {
        return "\\schemaVar \\termlabel " + name() + ";\n";
    }

    @Override
    public String toString() {
        return proofToString();
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
    public Sort sort() {
        return null;
    }

    @Override
    public Sort argSort(int i) {
        return null;
    }

    @Override
    public ImmutableArray<Sort> argSorts() {
        return null;
    }

    @Override
    public int arity() {
        return 0;
    }

    @Override
    public Sort sort(ImmutableArray<Term> terms) {
        return null;
    }

    @Override
    public boolean bindVarsAt(int n) {
        return false;
    }

    @Override
    public boolean isRigid() {
        return true;
    }

    @Override
    public boolean validTopLevel(Term term) {
        return true;
    }

    @Override
    public Name name() {
        return name;
    }

    @Override
    public boolean isStrict() {
        return false;
    }

    @Override
    public Object getChild(int i) {
        throw new IndexOutOfBoundsException();
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public Operator rename(Name name) {
        return new TermLabelSV(name);
    }
}