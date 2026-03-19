/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;

public class JavaDLOperatorUtil {
    /**
     * comparator to compare operators; for modalities only their kind is compared
     *
     * @param fst the first Operator
     * @param snd th second Operator
     * @return true iff both operators have same identity and for modalities if both are of the same
     *         kind
     */
    public static boolean opEquals(Operator fst,
            Operator snd) {
        return fst == snd ||
                (fst instanceof Modality mod1 && snd instanceof Modality mod2
                        && mod1.kind() == mod2.kind());
    }
}
