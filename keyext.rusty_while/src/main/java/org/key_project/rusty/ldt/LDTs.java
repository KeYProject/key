/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ldt;

import org.key_project.rusty.Services;

public class LDTs {
    private final BoolLDT boolLDT;
    private final IntLDT intLDT;

    public LDTs(Services services) {
        boolLDT = new BoolLDT(services);
        intLDT = new IntLDT(services);
    }

    public BoolLDT getBoolLDT() {
        return boolLDT;
    }

    public IntLDT getIntLDT() {
        return intLDT;
    }
}
