/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
