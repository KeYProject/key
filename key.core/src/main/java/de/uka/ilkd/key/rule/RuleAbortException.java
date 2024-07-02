// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule;

/**
 * 
 * @author jomi
 *
 *This Exception signals the abort of a rule Application
 *
 */


public class RuleAbortException extends Exception {

    private static final long serialVersionUID = -645034125571021135L;

    public RuleAbortException() {
        super("A rule application has been aborted");
    }
    
    public RuleAbortException(String msg) {
        super(msg);
    }
    
}