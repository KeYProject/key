package org.key_project.rusty.ast.ty;

import org.key_project.logic.Name;

import java.util.LinkedHashMap;
import java.util.Map;

public final class PrimitiveType implements  Type{
    private static final Map<Name, PrimitiveType> typeMap =
            new LinkedHashMap<>();

    public static final PrimitiveType U8 = new PrimitiveType(new Name("u8"));
    public static final PrimitiveType U16 = new PrimitiveType(new Name("u16"));
    public static final PrimitiveType U32 = new PrimitiveType(new Name("u32"));
    public static final PrimitiveType U64 = new PrimitiveType(new Name("u64"));
    public static final PrimitiveType USIZE = new PrimitiveType(new Name("usize"));
    public static final PrimitiveType I8 = new PrimitiveType(new Name("i8"));
    public static final PrimitiveType I16 = new PrimitiveType(new Name("i16"));
    public static final PrimitiveType I32 = new PrimitiveType(new Name("i32"));
    public static final PrimitiveType I64 = new PrimitiveType(new Name("i64"));
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
    public Name name() {
        return null;
    }

    @Override
    public String toString() {
        return name.toString();
    }
}
