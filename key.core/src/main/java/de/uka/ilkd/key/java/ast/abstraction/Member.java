/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.abstraction;

/**
 * A program model element representing members.
 */
public interface Member extends ProgramModelElement {

    /**
     * Checks if this member is final.
     *
     * @return <code>true</code> if this member is final, <code>false</code> otherwise.
     */
    boolean isFinal();

    /**
     * Checks if this member is static. Returns <code>true</code> for
     * {@code Constructor}s.
     *
     * @return <code>true</code> if this member is static, <code>false</code> otherwise.
     */
    boolean isStatic();

    /**
     * Checks if this member is private.
     *
     * @return <code>true</code> if this member is private, <code>false</code> otherwise.
     */
    boolean isPrivate();

    /**
     * Checks if this member is protected.
     *
     * @return <code>true</code> if this member is protected, <code>false</code> otherwise.
     */
    boolean isProtected();

    /**
     * Checks if this member is public.
     *
     * @return <code>true</code> if this member is public, <code>false</code> otherwise.
     */
    boolean isPublic();

    /**
     * Checks if this member is strictfp.
     *
     * @return <code>true</code> if this member is strictfp, <code>false</code> otherwise.
     */
    boolean isStrictFp();
}
