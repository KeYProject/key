package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

public class Epsilon extends AbstractOperator {
    private final Sort sort;

    public Epsilon(Sort sort) {
        super(new Name("eps"),1, new Boolean[]{true},true);
        this.sort = sort;
        /*
        super(new Name("\\eps"),
                new Sort[] {Sort.FORMULA},
                sort,
                new Boolean[]{true},
                true);*/
    }
/*
    @Override
    protected boolean additionalValidTopLevel2(Term term) {
        final Sort s0 = term.sub(0).sort();
        return s0 == Sort.FORMULA;
    }
*/
    @Override
    protected boolean additionalValidTopLevel(Term term) {


        final Sort s0 = term.sub(0).sort();
        return s0 == Sort.FORMULA;
    }

    @Override
    public Sort sort(ImmutableArray<Term> terms) {
        return sort;
    }

    @Override
    public int hashCode() {
        return name().hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (obj instanceof Epsilon) {
            Epsilon other = (Epsilon) obj;
            if (name().equals(other.name())) {
                return true;
                //return sort.equals(other.sort);
            }
        }
        return false;
    }
}
