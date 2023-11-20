/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.util.pp.Layouter;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

/**
 * Schema variable matching modal operators.
 */
public final class ModalOperatorSV extends Modality.JavaModalityKind implements SchemaVariable {

    /**
     * the set of modalities this sv can match
     */
    private final ImmutableSet<Modality.JavaModalityKind> modalities;


    /**
     * creates a new SchemaVariable that is used as placeholder for modal operators.
     *
     * @param name the Name of the SchemaVariable
     * @param modalityKinds modal operators matched by this SV
     */
    ModalOperatorSV(Name name, ImmutableSet<Modality.JavaModalityKind> modalityKinds) {
        super(name);
        this.modalities = modalityKinds;
    }

    /**
     * returns an unmodifiable set of operators this schemavariable can match
     */
    public ImmutableSet<Modality.JavaModalityKind> getModalities() {
        return modalities;
    }


    @Override
    public String toString() {
        // TODO: HACKS, remove new-line and re-generate taclets.old.txt
        return name().toString() + " (\n(modal operator))";
    }


    @Override
    public boolean isStrict() {
        return false;
    }

    @Override
    public void layout(Layouter<?> l) {
        l.beginC(0).beginC().print("\\schemaVar \\modalOperator {").brk(0);
        boolean first = true;
        for (Modality.JavaModalityKind modality : modalities) {
            if (!first) {
                l.print(",").brk();
            } else {
                first = false;
            }
            l.print(modality.name().toString());
        }
        l.end().brk(0).print("}").end().print(" ").print(name().toString());
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

        if (!(term.op() instanceof Modality)) {
            throw new TermCreationException("ModalOperatorSV must be contained in a modality");
        }
    }


    @Override
    public Sort sort() {
        throw new RuntimeException("Not supported");
    }

    @Override
    public int arity() {
        throw new RuntimeException("Not supported");
    }

    @Override
    public Sort sort(Sort[] sorts) {
        throw new RuntimeException("Not supported");
    }

    @Override
    public boolean bindVarsAt(int n) {
        throw new RuntimeException("Not supported");
    }

    @Override
    public boolean isRigid() {
        throw new RuntimeException("Not supported");
    }


    @Override
    public Sort argSort(int i) {
        throw new RuntimeException("Not supported");
    }

    @Override
    public ImmutableArray<Sort> argSorts() {
        throw new RuntimeException("Not supported");
    }

    @Override
    public final Modifier modifier() {
        // TODO: remove
        throw new RuntimeException("Not supported");
    }
}
