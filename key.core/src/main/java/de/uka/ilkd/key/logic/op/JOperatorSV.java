/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.sv.OperatorSV;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * Abstract base class for schema variables.
 */
public abstract class JOperatorSV extends JAbstractSortedOperator
        implements OperatorSV, SchemaVariable, Named {

    private final boolean isStrict;


    protected JOperatorSV(Name name, ImmutableArray<Sort> argSorts, Sort sort, boolean isRigid,
            boolean isStrict) {
        super(name, argSorts, sort, isRigid);
        this.isStrict = isStrict;
    }


    protected JOperatorSV(Name name, Sort[] argSorts, Sort sort, boolean isRigid,
            boolean isStrict) {
        this(name, new ImmutableArray<>(argSorts), sort, isRigid, isStrict);
    }


    protected JOperatorSV(Name name, Sort sort, boolean isRigid, boolean isStrict) {
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

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isTerm() {
        return false;
    }

    @Override
    public boolean isFormula() {
        return false;
    }

    @Override
    public boolean isSkolemTerm() {
        return false;
    }
}
