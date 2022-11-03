// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit;

import recoder.java.declaration.MemberDeclaration;

/**
 * Problem report indicating that a member declaration is not a valid member of an interface.
 */
public class IllegalInterfaceMember extends Conflict {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1632587249722947504L;
    private final MemberDeclaration member;

    public IllegalInterfaceMember(MemberDeclaration member) {
        this.member = member;
    }

    public MemberDeclaration getMember() {
        return member;
    }
}
