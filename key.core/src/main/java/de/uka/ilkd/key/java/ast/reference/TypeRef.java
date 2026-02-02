/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.reference;



import java.util.Objects;

import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;

public class TypeRef extends TypeReferenceImp {

    private final KeYJavaType kjt;

    /**
     * creates a type reference for the given KeYJavaType with dimension 0 and creates a suitable
     * package reference prefix from the KeYJavaType. If this is not desired use the constructor
     * TypeRef(ProgramElementName, int, ReferencePrefix, KeYJavaType) and take null as last
     * argument.
     */
    public TypeRef(@NonNull KeYJavaType kjt) {
        this(kjt, 0);
    }

    /**
     * creates a type reference for the given KeYJavaType and the given dimension and creates a
     * suitable package reference prefix from the KeYJavaType. If this is not desired use the
     * constructor TypeRef(ProgramElementName, int, ReferencePrefix, KeYJavaType) and take null as
     * last argument.
     */
    public TypeRef(@NonNull KeYJavaType kjt, int dim) {
        super(new ProgramElementName(kjt.getName()), dim, kjt.createPackagePrefix());
        this.kjt = kjt;
    }


    public TypeRef(ExtList children, KeYJavaType kjt, int dim) {
        super(children, dim);
        this.kjt = kjt;
    }

    public TypeRef(ProgramElementName name, int dimension, ReferencePrefix prefix,
            KeYJavaType kjt) {
        super(name, dimension, prefix);
        this.kjt = kjt;
    }

    public KeYJavaType getKeYJavaType() {
        return kjt;
    }

    /**
     * the KeYJavaType must eb part of the equality comparison to
     * ensure that the correct modalities are returned when looking up in the
     * cache.
     *
     * @param obj the Object to compare with
     * @return true if and only if both type references refer to the same type
     */
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj instanceof TypeRef tr) {
            return Objects.equals(kjt, tr.kjt) && super.equals(obj);
        }
        return false;
    }
}
