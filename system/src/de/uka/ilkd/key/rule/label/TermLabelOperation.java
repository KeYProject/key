package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.rule.MatchConditions;

/**
 * TermLabelOperations are used in goal templates of taclets to describe unions, set difference etc. operations
 * on labels.
 * 
 */
public abstract class TermLabelOperation implements ITermLabel, Named {

    private final Name name;
    private final ImmutableArray<ITermLabel> children;
    
    protected TermLabelOperation(String name, ITermLabel[] children) {
        this.name = new Name(name);
        this.children = new ImmutableArray<ITermLabel>(children);
    }

    @Override
    public int getChildCount() {
        return children.size();
    }
    
    @Override
    public int hashCode() {
        int hash = 0;
        for (final ITermLabel child : children) {
            hash += 17*child.hashCode();
        }
        return 23*name.hashCode() + hash;
    }
    
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TermLabelOperation)) {
            return false;
        }
        final TermLabelOperation cmp = (TermLabelOperation) o;
        if (cmp.getChildCount() != getChildCount() || 
                !cmp.name().equals(name())) {
            return false;
        }
        for (int i = 0; i<getChildCount(); i++) {
            if (!children.get(i).equals(cmp.children.get(i))) {
                return false;
            }
        }
        return true;
    }
    
    public ImmutableArray<ITermLabel> getChildren() {
        return children;
    }
    
    @Override
    public ITermLabel getChild(int i) {
        return children.get(i);
    }

    public abstract ImmutableArray<ITermLabel> evaluate(MatchConditions cond, Services services);
    
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append(name);
        result.append("(");
        for (ITermLabel l : children) {
            result.append(l);
            result.append(", ");
        }
        if (getChildCount() > 0) {
            result.deleteCharAt(result.length() - 1);
        }
        result.append(")");
        return result.toString();
    }

    @Override
    public Name name() {
        return name;
    }
    
}
