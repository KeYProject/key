/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.abstraction;

/**
 * A program model element representing methods.
 */
public interface Method extends Member, ClassTypeContainer {

    /**
     * Checks if this member is abstract. A constructor will report <CODE>false</CODE>.
     *
     * @return <CODE>true</CODE> if this member is abstract, <CODE>false</CODE> otherwise.
     * @see recoder.abstraction.Constructor
     */
    boolean isAbstract();

    /**
     * Checks if this method is native. A constructor will report <CODE>false</CODE>.
     *
     * @return <CODE>true</CODE> if this method is native, <CODE>false</CODE> otherwise.
     * @see recoder.abstraction.Constructor
     */
    boolean isNative();

    /**
     * Checks if this method is synchronized. A constructor will report <CODE>false</CODE>.
     *
     * @return <CODE>true</CODE> if this method is synchronized, <CODE>false</CODE> otherwise.
     * @see recoder.abstraction.Constructor
     */
    boolean isSynchronized();

}
