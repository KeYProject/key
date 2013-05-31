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


package de.uka.ilkd.key.util;

/**
 * Exception used by {@link CommandLine}.
 *
 * @see CommandLine
 */
@SuppressWarnings("serial")
public class CommandLineException extends Exception {

    /**
     * Instantiates a new command line exception without message.
     */
    public CommandLineException() {
        super();
    }

    /**
     * Instantiates a new command line exception.
     *
     * @param message
     *            an error message
     * @param cause
     *            the exception causing this exception
     */
    public CommandLineException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * Instantiates a new command line exception.
     *
     * @param message
     *            an error message
     */
    public CommandLineException(String message) {
        super(message);
    }

    /**
     * Instantiates a new command line exception.
     *
     * @param cause
     *            the exception causing this exception
     */
    public CommandLineException(Throwable cause) {
        super(cause);
    }

}
