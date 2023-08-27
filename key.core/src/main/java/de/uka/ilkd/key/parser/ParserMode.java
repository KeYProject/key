/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

/**
 * The mode in which the parser is currently running.
 *
 * The KeY parser goes over input files more than once. This enum is used to denote the mode of the
 * current run.
 */
public enum ParserMode {

    /**
     * Only parse declarations. Used to read in sort, predicate and function declarations.
     */
    DECLARATION,

    /**
     * Only parse terms.
     */
    TERM,

    /**
     * Parse global declarations.
     *
     * Apparently, this mode is only used in test case
     * {@link de.uka.ilkd.key.logic.TestClashFreeSubst}.
     */
    GLOBALDECL,

    /**
     * Only parse taclet definitions.
     *
     * Used by {@link KeYParser#parseTaclet(String, de.uka.ilkd.key.java.Services)}
     */
    TACLET,

    /**
     * Only parse the problem declaration at the end of a KeY input file.
     */
    PROBLEM;

    /**
     * Get the name of this parser mode.
     *
     * @return the same as {@link #toString()}
     */
    public String getName() {
        return toString();
    }
}
