/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

import recoder.java.Identifier;

public class LabelSVWrapper extends Identifier implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = 5338442155201858492L;
    SchemaVariable sv = null;

    public LabelSVWrapper(SchemaVariable sv) {
        this.sv = sv;
    }

    protected LabelSVWrapper(LabelSVWrapper proto) {
        super(proto);
        id = proto.id;
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
     * returns the schema variable of this label sv wrapper
     */
    public SchemaVariable getSV() {
        return sv;
    }


}
