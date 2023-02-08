// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.reference;

import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.list.generic.ASTList;

/**
 * This constructor reference.
 *
 * @author <TT>AutoDoc</TT>
 */

public class ThisConstructorReference extends SpecialConstructorReference {


    /**
     * serialization id
     */
    private static final long serialVersionUID = -4669357517439005903L;

    /**
     * This constructor reference.
     */

    public ThisConstructorReference() {
        makeParentRoleValid();
    }

    /**
     * This constructor reference.
     *
     * @param arguments an expression mutable list.
     */

    public ThisConstructorReference(ASTList<Expression> arguments) {
        super(arguments);
        makeParentRoleValid();
    }

    /**
     * This constructor reference.
     *
     * @param proto a this constructor reference.
     */

    protected ThisConstructorReference(ThisConstructorReference proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ThisConstructorReference deepClone() {
        return new ThisConstructorReference(this);
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): parameters
        if (arguments != null) {
            int index = arguments.indexOf(child);
            if (index >= 0) {
                return (index << 4) | 0;
            }
        }
        return -1;
    }

    public void accept(SourceVisitor v) {
        v.visitThisConstructorReference(this);
    }
}
