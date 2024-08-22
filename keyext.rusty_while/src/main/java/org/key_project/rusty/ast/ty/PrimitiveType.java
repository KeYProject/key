/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.ty;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.logic.Name;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;

public final class PrimitiveType implements Type {
    private static final Map<Name, PrimitiveType> typeMap =
        new LinkedHashMap<>();

    public static final PrimitiveType U8 = new PrimitiveType(new Name("u8"));
    public static final PrimitiveType U16 = new PrimitiveType(new Name("u16"));
    public static final PrimitiveType U32 = new PrimitiveType(new Name("u32"));
    public static final PrimitiveType U64 = new PrimitiveType(new Name("u64"));
    public static final PrimitiveType U128 = new PrimitiveType(new Name("u128"));
    public static final PrimitiveType USIZE = new PrimitiveType(new Name("usize"));
    public static final PrimitiveType I8 = new PrimitiveType(new Name("i8"));
    public static final PrimitiveType I16 = new PrimitiveType(new Name("i16"));
    public static final PrimitiveType I32 = new PrimitiveType(new Name("i32"));
    public static final PrimitiveType I64 = new PrimitiveType(new Name("i64"));
    public static final PrimitiveType I128 = new PrimitiveType(new Name("i128"));
    public static final PrimitiveType ISIZE = new PrimitiveType(new Name("isize"));
    public static final PrimitiveType BOOL = new PrimitiveType(new Name("bool"));
    public static final PrimitiveType CHAR = new PrimitiveType(new Name("char"));
    public static final PrimitiveType STR = new PrimitiveType(new Name("str"));
    public static final PrimitiveType NEVER = new PrimitiveType(new Name("!"));

    private final Name name;

    private PrimitiveType(Name name) {
        this.name = name;
        typeMap.put(name, this);
    }

    @Override
    public @NonNull Name name() {
        return name;
    }

    @Override
    public String toString() {
        return name.toString();
    }

    @Override
    public Sort getSort(Services services) {
        return switch (this.name().toString()) {
            case "U8", "U16", "U32", "U64", "U128", "USIZE", "I8", "I16", "I32", "I64", "I128", "ISIZE" -> services.getNamespaces().sorts().lookup("int");
            case "BOOL" -> services.getNamespaces().sorts().lookup("bool");
            default -> throw new RuntimeException("Unknown type " + this);
        };
    }
}
