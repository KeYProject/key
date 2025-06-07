/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;


import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableSet;

/**
 * Schema variable matching modal operators.
 */
public final class ModalOperatorSV extends JModality.JavaModalityKind
        implements SchemaVariable, Named {

    /**
     * the set of modalities this sv can match
     */
    private final ImmutableSet<JModality.JavaModalityKind> modalities;


    /**
     * creates a new SchemaVariable that is used as placeholder for modal operators.
     *
     * @param name the Name of the SchemaVariable
     * @param modalityKinds modal operators matched by this SV
     */
    ModalOperatorSV(Name name, ImmutableSet<JModality.JavaModalityKind> modalityKinds) {
        super(name);
        this.modalities = modalityKinds;
    }

    /**
     * returns an unmodifiable set of operators this schemavariable can match
     */
    public ImmutableSet<JModality.JavaModalityKind> getModalities() {
        return modalities;
    }


    @Override
    public String toString() {
        // TODO: HACKS, remove new-line and re-generate taclets.old.txt
        return name() + " ((modal operator))";
    }


    @Override
    public boolean isStrict() {
        return false;
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
