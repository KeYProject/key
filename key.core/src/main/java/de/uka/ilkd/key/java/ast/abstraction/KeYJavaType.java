/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.abstraction;

import java.util.Comparator;
import java.util.Objects;
import java.util.Optional;

import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.ast.reference.PackageReference;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * The KeY java type realises a tuple (sort, type) of a logic sort and the java type (for example a
 * class declaration). In contrast to other classes the KeYJavaType is <emph>not</emph> immutable,
 * so use it with care.
 */
@NullMarked
public class KeYJavaType implements Type {

    /** Special return "type" for void methods. */
    public static final KeYJavaType VOID_TYPE = new KeYJavaType(JavaDLTheory.ANY);

    /** the AST type */
    private @Nullable Type javaType = null;
    /** the logic sort */
    private @Nullable Sort sort = null;
    /**
     * Whether this is a synthetic, internal type (e.g. the {@code __Default__} default-execution-
     * context class) that should be hidden from user-facing type enumerations. Set once, at load,
     * before any concurrent read; see
     * {@link de.uka.ilkd.key.java.JavaInfo#getAllKeYJavaTypes(boolean)}.
     */
    private boolean internal = false;

    /** creates a new KeYJavaType */
    public KeYJavaType() {}

    /** creates a new KeYJavaType */
    public KeYJavaType(Type javaType, Sort sort) {
        this.javaType = Objects.requireNonNull(javaType);
        this.sort = Objects.requireNonNull(sort);
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Sort sort) {
        setSort(Objects.requireNonNull(sort));
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Type type) {
        setJavaType(Objects.requireNonNull(type));
    }

    public void setJavaType(@Nullable Type type) {
        javaType = type;
    }

    public void setSort(@Nullable Sort s) {
        sort = s;
    }

    public @Nullable Type getJavaType() {
        return javaType;
    }

    public @Nullable Sort getSort() {
        return sort;
    }

    /**
     * @return whether this is a synthetic, internal type that is hidden from user-facing type
     *         enumerations (see {@link #markInternal()})
     */
    public boolean isInternal() {
        return internal;
    }

    /**
     * Marks this type as synthetic/internal so it stays out of user-facing enumerations
     * ({@link de.uka.ilkd.key.java.JavaInfo#getAllKeYJavaTypes(boolean)}).
     */
    public void markInternal() {
        this.internal = true;
    }

    /**
     * Returns the default value of the given type according to JLS Sect. 4.5.5; returns null if
     * this is not a real Java type.
     *
     * @return the default value of the given type according to JLS Sect. 4.5.5
     */
    public @Nullable Literal getDefaultValue() {
        if (javaType == null) {
            return null;
        }
        return javaType.getDefaultValue();
    }

    public String toString() {
        if (this == VOID_TYPE) {
            return "KeYJavaType:void";
        }
        if (javaType == null) {
            return "KeYJavaType:null," + sort;
        }
        return "(type, sort): (" + javaType.getName() + "," + sort + ")";
    }

    public String getFullName() {
        return Optional.ofNullable(getJavaType()).map(Type::getFullName)
                .orElse(
                    getSort() != null ? getSort().name().toString() : "This should never be seen");
    }

    public String getName() {
        if (javaType != null) {
            return javaType.getName();
        } else {
            assert sort != null;
            return sort.name().toString();
        }
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        try {
            return (Objects.equals(javaType, ((KeYJavaType) o).javaType))
                    && Objects.equals(sort, ((KeYJavaType) o).sort);
        } catch (Exception e) {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return getFullName().hashCode();
    }


    public PackageReference createPackagePrefix() {
        PackageReference ref = null;
        String rest = getFullName();
        if (rest.indexOf('.') > 0) {
            rest = rest.substring(0, rest.lastIndexOf('.') + 1);
            while (rest.indexOf('.') > 0) {
                String name = rest.substring(0, rest.indexOf('.'));
                rest = rest.substring(rest.indexOf('.') + 1);
                ref = new PackageReference(new ProgramElementName(name), ref);
            }
        }
        return ref;
    }

    public static final class LexicographicalKeYJavaTypeOrder<T extends KeYJavaType>
            implements Comparator<T> {
        public int compare(T arg0, T arg1) {
            return arg0.getFullName().compareTo(arg1.getFullName());
        }
    }
}
