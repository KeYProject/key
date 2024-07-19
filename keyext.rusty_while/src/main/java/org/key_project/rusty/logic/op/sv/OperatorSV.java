package org.key_project.rusty.logic.op.sv;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

public abstract class OperatorSV extends AbstractSortedOperator implements SchemaVariable {
    private final boolean isStrict;


    protected OperatorSV(Name name, ImmutableArray<Sort> argSorts, Sort sort, boolean isRigid,
                         boolean isStrict) {
        super(name, argSorts, sort, isRigid ? Modifier.RIGID : Modifier.NONE);
        this.isStrict = isStrict;
    }


    protected OperatorSV(Name name, Sort[] argSorts, Sort sort, boolean isRigid, boolean isStrict) {
        this(name, new ImmutableArray<>(argSorts), sort, isRigid, isStrict);
    }


    protected OperatorSV(Name name, Sort sort, boolean isRigid, boolean isStrict) {
        this(name, new ImmutableArray<>(), sort, isRigid, isStrict);
    }


    protected final String toString(String sortSpec) {
        return name() + " (" + sortSpec + ")";
    }


    @Override
    public final boolean isStrict() {
        return isStrict;
    }

    @Override
    public void validTopLevelException(Term term) throws TermCreationException {
        if (arity() != term.arity()) {
            throw new TermCreationException(this, term);
        }

        if (arity() != term.subs().size()) {
            throw new TermCreationException(this, term);
        }

        for (int i = 0; i < arity(); i++) {
            if (term.sub(i) == null) {
                throw new TermCreationException(this, term);
            }
        }

    }
}
