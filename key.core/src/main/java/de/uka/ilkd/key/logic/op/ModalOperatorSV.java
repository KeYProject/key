/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;


import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/**
 * Schema variable matching modal operators.
 */
public final class ModalOperatorSV extends JModality.JavaModalityKind
        implements SchemaVariable {

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
    public @NonNull String toString() {
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

    // Operator interface methods (irrelevant for this kind of SV)
    @Override
    public @NonNull Sort argSort(int i) {
        throw new IndexOutOfBoundsException("A JavaModalityKind does not have arguments.");
    }

    @Override
    public @NonNull ImmutableArray<Sort> argSorts() {
        return new ImmutableArray<>();
    }

    @Override
    public @NonNull Sort sort() {
        throw new UnsupportedOperationException("A JavaModalityKind does not have a sort.");
    }

    @Override
    public int arity() {
        return 0;
    }

    @Override
    public @NonNull Sort sort(@NonNull Sort @NonNull [] sorts) {
        throw new IndexOutOfBoundsException("A JavaModalityKind does not have a sort.");
    }

    @Override
    public boolean bindVarsAt(int n) {
        return false;
    }

    @Override
    public @NonNull Modifier modifier() {
        return Modifier.NONE;
    }

    @Override
    public boolean hasModifier(@NonNull Modifier mod) {
        return SchemaVariable.super.hasModifier(mod);
    }

    @Override
    public boolean isRigid() {
        return false;
    }

    @Override
    public <T extends Term> void validTopLevelException(T term) throws TermCreationException {
        throw new TermCreationException("ModalOperatorSV should not be checked" +
            " via this method as it is not an actual operator");
    }

}
