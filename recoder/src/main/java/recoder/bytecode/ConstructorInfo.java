// This file is part of the RECODER library and protected by the LGPL.

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
