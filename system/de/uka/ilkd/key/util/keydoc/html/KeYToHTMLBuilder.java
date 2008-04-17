// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.util.keydoc.html;

import java.io.*;


/** The abstract builder class.
 */
abstract class KeYToHTMLBuilder {
	
    /** Every builder must be able to build the HTML representation of a key documentation.
	@param toBuild .key file, for which the documentation should be processed
	@return an object of the class type {@link de.uka.ilkd.key.util.keydoc.html.BoxedFile}
    */
    protected static BoxedFile buildHTMLFile(File toBuild) {
    	return null;
    }

}
