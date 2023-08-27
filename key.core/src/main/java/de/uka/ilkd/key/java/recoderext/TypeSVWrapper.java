/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

import recoder.java.SourceElement;
import recoder.java.reference.TypeReference;

public class TypeSVWrapper extends TypeReference implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = 2694567717981292433L;
    SchemaVariable sv = null;

    public TypeSVWrapper(SchemaVariable sv) {
        this.sv = sv;
    }

    protected TypeSVWrapper(TypeSVWrapper proto) {
        super(proto);
    }

    /**
     * sets the schema variable of sort label
     *
     * @param sv the SchemaVariable
     */
    public void setSV(SchemaVariable sv) {
        this.sv = sv;
    }

    /**
     * returns the schema variable of this type sv wrapper
     */
    public SchemaVariable getSV() {
        return sv;
    }

    public SourceElement getFirstElement() {
        return this;
    }


}
