/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import java.util.List;

/**
 * A program model element representing members.
 *
 * @author AL
 * @author RN
 */
public interface Member extends ProgramModelElement {

    /**
     * Checks if this member is final.
     *
     * @return <CODE>true</CODE> if this member is final, <CODE>false</CODE> otherwise.
     */
    boolean isFinal();

    /**
     * Checks if this member is static. Returns <CODE>true</CODE> for
     * {@link recoder.abstraction.Constructor}s.
     *
     * @return <CODE>true</CODE> if this member is static, <CODE>false
     * </CODE> otherwise.
     */
    boolean isStatic();

    /**
     * Checks if this member is private.
     *
     * @return <CODE>true</CODE> if this member is private, <CODE>false
     * </CODE> otherwise.
     */
    boolean isPrivate();

    /**
     * Checks if this member is protected.
     *
     * @return <CODE>true</CODE> if this member is protected, <CODE>false
     * </CODE> otherwise.
     */
    boolean isProtected();

    /**
     * Checks if this member is public.
     *
     * @return <CODE>true</CODE> if this member is public, <CODE>false
     * </CODE> otherwise.
     */
    boolean isPublic();

    /**
     * Checks if this member is strictfp.
     *
     * @return <CODE>true</CODE> if this member is strictfp, <CODE>false
     * </CODE> otherwise.
     */
    boolean isStrictFp();

    /**
     * Returns the logical parent class of this member.
     *
     * @return the class type containing this member.
     */
    ClassType getContainingClassType();

    /**
     * Returns a list of Annotations.
     *
     * @return the annotations
     */
    List<? extends AnnotationUse> getAnnotations();
}
