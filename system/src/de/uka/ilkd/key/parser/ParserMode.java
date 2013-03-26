// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.parser;

/**
 * The mode in which the parser is currently running.
 * 
 * The KeY parser goes over input files more than once. This enum is used to
 * denote the mode of the current run.
 */
public enum ParserMode {

    /**
     * Only parse declarations. Used to read in sort, predicate and function
     * declarations.
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
     * Used by
     * {@link KeYParser#parseTaclet(String, de.uka.ilkd.key.java.Services)}
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
