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

package de.uka.ilkd.key.logic.label;

/**
 * An exception which can be thrown by the term label system.
 *
 * <p>
 * {@link TermLabelFactory} methods can throw an instance if the requested term
 * label cannot be created.
 *
 * <p>
 * {@link TermLabelManager} can throw this if a requested label name has not
 * been registered.
 *
 * @author mattias ulbrich
 */

@SuppressWarnings("serial")
public class TermLabelException extends Exception {

    public TermLabelException() {
        super();
    }

    public TermLabelException(String message, Throwable cause) {
        super(message, cause);
    }

    public TermLabelException(String message) {
        super(message);
    }

    public TermLabelException(Throwable cause) {
        super(cause);
    }

}