/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.ast.abstraction.KeYRustyType;

public class NewVarcond implements org.key_project.prover.rules.NewVarcond {
    private final org.key_project.logic.op.sv.SchemaVariable sv;
    private final org.key_project.logic.op.sv.SchemaVariable peerSV;
    private final KeYRustyType type;

    public NewVarcond(org.key_project.logic.op.sv.SchemaVariable sv,
            org.key_project.logic.op.sv.SchemaVariable peerSV) {
        assert sv != null;
        assert peerSV != null;
        this.sv = sv;
        this.peerSV = peerSV;
        type = null;
    }

    public NewVarcond(org.key_project.logic.op.sv.SchemaVariable sv, KeYRustyType type) {
        assert sv != null;
        assert type != null;
        this.sv = sv;
        this.peerSV = null;
        this.type = type;
    }

    public org.key_project.logic.op.sv.SchemaVariable getSchemaVariable() {
        return sv;
    }

    public SchemaVariable getPeerSchemaVariable() {
        return peerSV;
    }

    public KeYRustyType getType() {
        return type;
    }

    public Object getTypeDefiningObject() {
        return type != null ? type : peerSV;
    }
}
