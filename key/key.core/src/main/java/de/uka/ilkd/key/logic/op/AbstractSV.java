package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Abstract base class for schema variables.
 */
public abstract class AbstractSV extends AbstractSortedOperator implements SchemaVariable {

    private final boolean isStrict;


    protected AbstractSV(Name name, ImmutableArray<Sort> argSorts, Sort sort, boolean isRigid,
            boolean isStrict) {
        super(name, argSorts, sort, isRigid);
        this.isStrict = isStrict;
    }


    protected AbstractSV(Name name, Sort[] argSorts, Sort sort, boolean isRigid, boolean isStrict) {
        this(name, new ImmutableArray<Sort>(argSorts), sort, isRigid, isStrict);
    }


    protected AbstractSV(Name name, Sort sort, boolean isRigid, boolean isStrict) {
        this(name, (ImmutableArray<Sort>) null, sort, isRigid, isStrict);
    }


    protected final String toString(String sortSpec) {
        return name() + " (" + sortSpec + ")";
    }


    @Override
    public final boolean isStrict() {
        return isStrict;
    }
}
