/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;
import de.uka.ilkd.key.logic.op.OperatorSV;

public class MethodSignatureSVWrapper extends MethodSignature implements SVWrapper {

    private static final long serialVersionUID = -4381850332826267659L;
    private final OperatorSV method;

    public MethodSignatureSVWrapper(OperatorSV l) {
        super(null, null);
        method = l;
    }

    public OperatorSV getSV() {
        return method;
    }

    public String toString() {
        return String.valueOf(method);
    }
}
