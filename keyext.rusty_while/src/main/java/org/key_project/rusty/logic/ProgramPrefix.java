/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.util.collection.ImmutableArray;

/**
 * this interface is implemented by program elements that may be matched by the inactive program
 * prefix
 */
public interface ProgramPrefix extends RustyProgramElement {
    /** return true if there is a next prefix element */
    boolean hasNextPrefixElement();

    /**
     * return the next prefix element if no next prefix element is available an
     * IndexOutOfBoundsException is thrown
     */
    ProgramPrefix getNextPrefixElement();

    /** return the last prefix element */
    ProgramPrefix getLastPrefixElement();

    /**
     * returns an array with all prefix elements starting at this element
     */
    ImmutableArray<ProgramPrefix> getPrefixElements();

    /** returns the position of the first active child */
    PosInProgram getFirstActiveChildPos();

    /** returns the length of the prefix */
    int getPrefixLength();
}
