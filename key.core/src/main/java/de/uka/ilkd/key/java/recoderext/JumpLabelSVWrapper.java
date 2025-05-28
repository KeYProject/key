/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.JOperatorSV;

public class JumpLabelSVWrapper implements SVWrapper {

    private final JOperatorSV label;

    public JumpLabelSVWrapper(JOperatorSV l) {
        label = l;
    }

    public JOperatorSV getSV() {
        return label;
    }

    public String toString() {
        return String.valueOf(label);
    }

}
