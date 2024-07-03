/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTList;

/**
 * Extends.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Extends extends InheritanceSpecification {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 8407322782204527496L;

    /**
     * Extends.
     */

    public Extends() {
        // nothing to do here
    }

    /**
     * Extends.
     *
     * @param supertype a type reference.
     */

    public Extends(TypeReference supertype) {
        super(supertype);
        makeParentRoleValid();
    }

    /**
     * Extends.
     *
     * @param list a type reference mutable list.
     */

    public Extends(ASTList<TypeReference> list) {
        super(list);
        makeParentRoleValid();
    }

    /**
     * Extends.
     *
     * @param proto an extends.
     */

    protected Extends(Extends proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Extends deepClone() {
        return new Extends(this);
    }

    public void accept(SourceVisitor v) {
        v.visitExtends(this);
    }
}
