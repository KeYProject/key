/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import recoder.abstraction.Constructor;
import recoder.convenience.Naming;

public class ConstructorInfo extends MethodInfo implements Constructor {

    public ConstructorInfo(int accessFlags, String name, String[] paramtypes, String[] exceptions,
            ClassFile cf) {
        super(accessFlags, null, name, paramtypes, exceptions, cf);
    }

    public String getFullName() {
        return Naming.getFullName(this);
        /*
         * ClassType ct = getContainingClassType(); if (ct == null) { throw new
         * RuntimeException("No class found for " + getName()); } return ct.getFullName();
         */
    }
}
