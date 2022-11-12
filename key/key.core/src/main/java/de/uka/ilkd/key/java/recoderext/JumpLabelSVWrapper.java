/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.SchemaVariable;

public class JumpLabelSVWrapper implements SVWrapper {

    private SchemaVariable label;

    public JumpLabelSVWrapper(SchemaVariable l) {
        label = l;
    }

    public SchemaVariable getSV() {
        return label;
    }

    public void setSV(SchemaVariable sv) {
        label = sv;
    }

    public String toString() {
        return "" + label;
    }

}
