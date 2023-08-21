/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import recoder.abstraction.Member;

/**
 * Problem report indicating that a member has been overwritten that was declared final, or was in a
 * final type.
 */
public class FinalOverwrite extends Conflict {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -4261490216982913161L;
    private final Member member;

    public FinalOverwrite(Member member) {
        this.member = member;
    }

    public Member getMember() {
        return member;
    }
}
