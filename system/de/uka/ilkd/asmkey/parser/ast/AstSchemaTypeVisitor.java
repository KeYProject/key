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

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;

/** Visitor for schema types.
 *
 * @see AstSchemaType
 * @author Hubert Schmid
 */

public interface AstSchemaTypeVisitor {

    /** Primitive schema type. */
    void visitPrimitive(PrimitiveSchemaType type, boolean rigid, Location location)
	throws ParserException;

    /** Schema type composed of a sort.  */
    void visitComposed(AstType sort, boolean rigid, Location location)
	throws ParserException;

    /** the schema variable matches only logical variables.*/
    void visitVariable(AstType sort, Location location)
	throws ParserException;

    /** Schema type for depending variables (skolem functions). */
    void visitDepending(AstType sort, Location location)
	throws ParserException;

}
