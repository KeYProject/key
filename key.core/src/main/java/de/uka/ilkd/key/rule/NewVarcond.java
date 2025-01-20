/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * variable condition used if a new variable is introduced
 */
public class NewVarcond {

    private final SchemaVariable sv;
    private final SchemaVariable peerSV;
    private final KeYJavaType type;


    /*
     * @param sv the Schemavariable representing a new variable.
     *
     * @param peerSV a Schemavariable defining the type of the new variable.
     */
    public NewVarcond(SchemaVariable sv, SchemaVariable peerSV) {
        assert sv != null;
        assert peerSV != null;
        this.sv = sv;
        this.peerSV = peerSV;
        this.type = null;
    }


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
