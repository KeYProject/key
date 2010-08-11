// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser;


import de.uka.ilkd.key.util.Service;


/** Factory class to create instances of SimpleTermParser.
 *
 * @author Hubert Schmid */

public final class TermParserFactory {

    /* --- static methods --- */

    public static final SimpleTermParser createInstance() {
	return (SimpleTermParser) Service.find(SimpleTermParser.class.getName(),
					       DefaultTermParser.class.getName());
    }

}
