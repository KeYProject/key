/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule;


import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;

import org.key_project.logic.op.sv.SchemaVariable;

/**
 * Variable condition that introduces a new variable into a taclet. The sort of the new variable
 * is defined by the second argument: either an explicit Java type ({@code \new(sv, T)}), a sort
 * ({@code \new(sv, S)}), or the type of another schema variable
 * ({@code \new(sv, \typeof(otherSV))}); the latter form is also used for {@code \newTypeOf}.
 */
public class NewVarcond implements org.key_project.prover.rules.conditions.NewVarcond {

    private final SchemaVariable sv;
    private final SchemaVariable peerSV;
    private final KeYJavaType type;

    /**
     * Creates a condition that introduces {@code sv} with the type of the schema variable
     * {@code peerSV}.
     *
     * @param sv the schema variable representing the new variable
     * @param peerSV the schema variable that defines the type of the new variable
     */
    public NewVarcond(SchemaVariable sv, SchemaVariable peerSV) {
        assert sv != null;
        assert peerSV != null;
        this.sv = sv;
        this.peerSV = peerSV;
        this.type = null;
    }

    /**
     * Creates a condition that introduces {@code sv} with the given Java type.
     *
     * @param sv the schema variable representing the new variable
     * @param type the Java type of the new variable
     */
    public NewVarcond(SchemaVariable sv, KeYJavaType type) {
        assert sv != null;
        assert type != null;
        this.sv = sv;
        this.peerSV = null;
        this.type = type;
    }

    public boolean isDefinedByType() {
        return peerSV == null;
    }


    public SchemaVariable getSchemaVariable() {
        return sv;
    }


    public SchemaVariable getPeerSchemaVariable() {
        return peerSV;
    }


    public KeYJavaType getType() {
        return type;
    }


    public Object getTypeDefiningObject() {
        return type != null ? type : peerSV;
    }


    @Override
    public String toString() {
        return "\\new(" + sv + ", "
            + (type != null ? String.valueOf(type) : "\\typeof(" + peerSV + ")") + ")";
    }
}
