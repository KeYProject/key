/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration;

import recoder.java.Declaration;

/**
 * Member declaration.
 *
 * @author <TT>AutoDoc</TT>
 */

public interface MemberDeclaration extends Declaration {

    /**
     * Get member parent.
     *
     * @return the type declaration.
     */
    TypeDeclaration getMemberParent();

    /**
     * does *not* add to parent's children list automatically
     */
    void setMemberParent(TypeDeclaration t);

    /**
     * Test whether the declaration is private.
     */
    boolean isPrivate();

    /**
     * Test whether the declaration is protected.
     */
    boolean isProtected();

    /**
     * Test whether the declaration is public.
     */
    boolean isPublic();

    /**
     * Test whether the declaration is static.
     */
    boolean isStatic();

    /**
     * Test whether the declaration is strictfp.
     */
    boolean isStrictFp();
}
