/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.statement.MethodFrame;

import org.key_project.util.collection.ImmutableArray;

/**
 * this interface is implemented by program elements that may be matched by the inactive program
 * prefix
 */
public interface PossibleProgramPrefix extends NonTerminalProgramElement {

    default boolean isPrefix() { return true; }

    /** return true if there is a next prefix element */
    boolean hasNextPrefixElement();

    /**
     * return the next prefix element if no next prefix element is available an
     * IndexOutOfBoundsException is thrown
     */
    PossibleProgramPrefix getNextPrefixElement();

    /** return the last prefix element */
    PossibleProgramPrefix getLastPrefixElement();

    /**
     * returns an array with all prefix elements starting at this element
     */
    ImmutableArray<PossibleProgramPrefix> getPrefixElements();

    /** returns the position of the first active child */
    PosInProgram getFirstActiveChildPos();

    /** returns the length of the prefix */
    int getPrefixLength();

    /** returns the innermost {@link MethodFrame} */
    MethodFrame getInnerMostMethodFrame();

}
