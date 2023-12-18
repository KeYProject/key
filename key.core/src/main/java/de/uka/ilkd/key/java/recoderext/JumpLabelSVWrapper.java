/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.AbstractSV;

public class JumpLabelSVWrapper implements SVWrapper {

    private final AbstractSV label;

    public JumpLabelSVWrapper(AbstractSV l) {
        label = l;
    }

    public AbstractSV getSV() {
        return label;
    }

    public String toString() {
        return String.valueOf(label);
    }

}
