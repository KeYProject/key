/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import java.util.List;

import recoder.abstraction.TypeArgument;

/**
 * @author Tobias Gutzmann
 */
public class TypeArgumentInfo implements TypeArgument {
    final WildcardMode wildcardMode;
    final String typeName;
    final List<? extends TypeArgument> typeArgs;
    final boolean isTypeVariable;
    ByteCodeElement parent;

    /**
     *
     */
    public TypeArgumentInfo(WildcardMode wildcardMode, String typeName,
            List<? extends TypeArgument> typeArgs, ByteCodeElement parent, boolean isTypeVariable) {
        super();
        if ((typeName == null && wildcardMode != WildcardMode.Any) || wildcardMode == null
                || parent == null) {
            throw new NullPointerException();
        }
        this.wildcardMode = wildcardMode;
        this.typeName = typeName;
        this.typeArgs = typeArgs;
        this.isTypeVariable = isTypeVariable;
        this.parent = parent;
    }

    public WildcardMode getWildcardMode() {
        return wildcardMode;
    }

    public String getTypeName() {
        return typeName;
    }

    public List<? extends TypeArgument> getTypeArguments() {
        return typeArgs;
    }

    public boolean isTypeVariable() {
        return isTypeVariable;
    }

    public ClassFile getContainingClassFile() {
        if (parent instanceof ClassFile) {
            return (ClassFile) parent;
        } else {
            return (ClassFile) ((MethodInfo) parent).getContainingClassType();
        }
    }

    public MethodInfo getContainingMethodInfo() {
        if (parent instanceof MethodInfo) {
            return (MethodInfo) parent;
        }
        return null;
    }

}
