/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

/**
 * Implements.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Implements extends InheritanceSpecification {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 8977810702311137411L;

    /**
     * Implements.
     */

    public Implements() {
        // nothing to do here
    }

    /**
     * Implements.
     *
     * @param supertype a type reference.
     */

    public Implements(TypeReference supertype) {
        super(supertype);
        makeParentRoleValid();
    }

    /**
     * Implements.
     *
     * @param list a type reference mutable list.
     */

    public Implements(ASTList<TypeReference> list) {
        super(list);
        makeParentRoleValid();
    }

    /**
     * Implements.
     *
     * @param proto an implements.
     */

    protected Implements(Implements proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Implements deepClone() {
        return new Implements(this);
    }

    public void accept(SourceVisitor v) {
        v.visitImplements(this);
    }
}
