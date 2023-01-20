// This file is part of the RECODER library and protected by the LGPL.

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
