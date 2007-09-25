// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.ast;


import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.parser.Location;


/** Identifier consists of a string and a location of the string in
 * the input.
 *
 * @author Hubert Schmid
 */

public final class Identifier extends AstNode implements Named {

    /** The actual text of the identifier. */
    private final String text;

    private final Name name;

    /** Creates an identifier with the given name that occurs at the
     * given position in the input stream. */
    public Identifier(Location location, String text) {
        super(location);
        this.text = text;
	this.name = new Name(text);
    }


    /** Returns the actual text of the identifier. */
    public String getText() {
        return text;
    }

    public Name name() {
	return name;
    }

    /** for debug only */
    public String toString() {
        return "[Id:" + text + "]";
    }

}
