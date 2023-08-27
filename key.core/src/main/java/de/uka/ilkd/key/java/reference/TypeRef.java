/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.util.ExtList;

public class TypeRef extends TypeReferenceImp {

    private KeYJavaType kjt = null;

    /**
     * creates a type reference for the given KeYJavaType with dimension 0 and creates a suitable
     * package reference prefix from the KeYJavaType. If this is not desired use the constructor
     * TypeRef(ProgramElementName, int, ReferencePrefix, KeYJavaType) and take null as last
     * argument.
     */
    public TypeRef(KeYJavaType kjt) {
        this(kjt, 0);
    }

    /**
     * creates a type reference for the given KeYJavaType and the given dimension and creates a
     * suitable package reference prefix from the KeYJavaType. If this is not desired use the
     * constructor TypeRef(ProgramElementName, int, ReferencePrefix, KeYJavaType) and take null as
     * last argument.
     */
    public TypeRef(KeYJavaType kjt, int dim) {
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

}
