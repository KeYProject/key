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

package de.uka.ilkd.key.parser;


/** This class represents an error of a parser.
 *
 * @author Hubert Schmid
 */

public final class ParserException extends Exception {

    /* --- constructors --- */

    /**
     * 
     */
    private static final long serialVersionUID = -5701137989453187397L;


    /** @param message The error message. The message may be shown to
     * the user and should be appropriately formated.
     * @param location The location on which the error occured. The
     * location may be null, if the location is unknown or the error
     * is independent of a location. */
    public ParserException(String message, Location location) {
        super(message);
        this.location = location;
    }


    /* --- methods --- */

    /** @return The location may be null. */
    public Location getLocation() {
        return location;
    }


    /* --- fields --- */

    private final Location location;

}