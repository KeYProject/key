/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.abstraction;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.ty.PrimitiveRustType;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ldt.BoolLDT;
import org.key_project.rusty.ldt.IntLDT;

import org.jspecify.annotations.NonNull;

public final class PrimitiveType implements Type {
    private static final Map<Name, PrimitiveType> typeMap =
        new LinkedHashMap<>();
    private static final Map<Name, PrimitiveType> ldtMap = new LinkedHashMap<>();

    public static final PrimitiveType U8 = new PrimitiveType(new Name("u8"), IntLDT.NAME);
    public static final PrimitiveType U16 = new PrimitiveType(new Name("u16"), IntLDT.NAME);
    public static final PrimitiveType U32 = new PrimitiveType(new Name("u32"), IntLDT.NAME);
    public static final PrimitiveType U64 = new PrimitiveType(new Name("u64"), IntLDT.NAME);
    public static final PrimitiveType U128 = new PrimitiveType(new Name("u128"), IntLDT.NAME);
    public static final PrimitiveType USIZE = new PrimitiveType(new Name("usize"), IntLDT.NAME);
    public static final PrimitiveType I8 = new PrimitiveType(new Name("i8"), IntLDT.NAME);
    public static final PrimitiveType I16 = new PrimitiveType(new Name("i16"), IntLDT.NAME);
    public static final PrimitiveType I32 = new PrimitiveType(new Name("i32"), IntLDT.NAME);
    public static final PrimitiveType I64 = new PrimitiveType(new Name("i64"), IntLDT.NAME);
    public static final PrimitiveType I128 = new PrimitiveType(new Name("i128"), IntLDT.NAME);
    public static final PrimitiveType ISIZE = new PrimitiveType(new Name("isize"), IntLDT.NAME);
    public static final PrimitiveType BOOL = new PrimitiveType(new Name("bool"), BoolLDT.NAME);
    public static final PrimitiveType CHAR = new PrimitiveType(new Name("char"), null);
    public static final PrimitiveType STR = new PrimitiveType(new Name("str"), null);
    public static final PrimitiveType NEVER = new PrimitiveType(new Name("!"), null);

    private final Name name;
    private final Name ldtName;

    private PrimitiveType(Name name, Name ldtName) {
        this.name = name;
        this.ldtName = ldtName;
        typeMap.put(name, this);
        if (ldtName != null) {
            ldtMap.put(ldtName, this);
        }
    }

    public static PrimitiveType get(String name) {
        return typeMap.get(new Name(name));
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
        var sort = services.getNamespaces().sorts().lookup(name);
        if (sort == null)
            throw new RuntimeException("Unknown type " + this);
        return sort;
    }

    /**
     * Gets the name of the LDT corresponding to this primitive type.
     *
     * @return may be null if no name set
     */
    public Name getCorrespondingLDTName() {
        return ldtName;
    }

    @Override
    public RustType toRustType(Services services) {
        return new PrimitiveRustType(this);
    }
}
