/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.util.pp.Layouter;

import org.key_project.logic.Name;
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
        return name().toString() + " ((modal operator))";
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
}
