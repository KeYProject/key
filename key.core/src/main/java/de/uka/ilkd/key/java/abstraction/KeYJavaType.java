/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.abstraction;

import java.util.Comparator;
import java.util.Objects;
import java.util.Optional;

import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * The KeY java type realises a tuple (sort, type) of a logic sort and the java type (for example a
 * class declaration). In contrast to other classes the KeYJavaType is <emph>not</emph> immutable,
 * so use it with care.
 */
public class KeYJavaType implements Type {

    /** Special return "type" for void methods. */
    public static final KeYJavaType VOID_TYPE = new KeYJavaType(null, Sort.ANY);

    /** the AST type */
    private Type javaType = null;
    /** the logic sort */
    private Sort sort = null;

    /** creates a new KeYJavaType */
    public KeYJavaType() {
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Type javaType, Sort sort) {
        this.javaType = javaType;
        this.sort = sort;
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Sort sort) {
        this.sort = sort;
    }

    /** creates a new KeYJavaType */
    public KeYJavaType(Type type) {
        this.javaType = type;
    }

    public void setJavaType(Type type) {
        javaType = type;
    }

    public void setSort(Sort s) {
        sort = s;
    }

    public Type getJavaType() {
        return javaType;
    }

    public Sort getSort() {
        return sort;
    }

    /**
     * Returns the default value of the given type according to JLS Sect. 4.5.5; returns null if
     * this is not a real Java type.
     *
     * @return the default value of the given type according to JLS Sect. 4.5.5
     */
    public Literal getDefaultValue() {
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
                .orElse(getSort().name().toString());
    }

    public String getName() {
        return Optional.ofNullable(getJavaType()).map(Type::getName)
                .orElse(getSort().name().toString());
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
            return Objects.equals(javaType, ((KeYJavaType) o).javaType)
                    && Objects.equals(sort, ((KeYJavaType) o).sort);
        } catch (Exception e) {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return 0;
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
