/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import java.util.List;

import recoder.abstraction.Field;
import recoder.abstraction.Type;
import recoder.convenience.Naming;

public class FieldInfo extends MemberInfo implements Field {

    protected final String type;

    protected final String constantValue;

    protected final List<TypeArgumentInfo> typeArgs;

    public FieldInfo(int accessFlags, String name, String type, ClassFile cf, String constantValue,
            List<TypeArgumentInfo> typeArgs) {
        super(accessFlags, name, cf);
        this.type = type;
        this.constantValue = constantValue;
        this.typeArgs = typeArgs;
    }

    public final String getTypeName() {
        return type;
    }

    // can be null
    public final String getConstantValue() {
        return constantValue;
    }

    public Type getType() {
        return service.getType(this);
    }

    public String getFullName() {
        return Naming.getFullName(this);
        /*
         * ClassType ct = getContainingClassType(); if (ct == null) { throw new
         * RuntimeException("No class found for " + getName()); } return
         * Naming.dot(ct.getFullName(), getName());
         */
    }

    public List<TypeArgumentInfo> getTypeArguments() {
        return typeArgs;
    }
}
