package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;

public class TermLabelWildcard extends TermLabelOperation implements SchemaVariable, ITermLabel {
    
    public static TermLabelWildcard WILDCARD = new TermLabelWildcard();
    
    private TermLabelWildcard() {
        super("*", new ITermLabel[0]);
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
        // should never be used as an operator of class term
        return false;
    }

    @Override
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        
        return null;
    }

    @Override
    public boolean isStrict() {
        return false;
    }

    @Override
    public String proofToString() {
        return name().toString();
    }

    @Override
    public ITermLabel getChild(int i) {
        throw new IndexOutOfBoundsException();
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @SuppressWarnings("unchecked")
    @Override
    public ImmutableArray<ITermLabel> evaluate(MatchConditions cond,
            Services services) {
        return (ImmutableArray<ITermLabel>) cond.getInstantiations().getInstantiation(this);
    }

}
