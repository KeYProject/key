// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser;


import java.io.File;
import java.io.FileNotFoundException;
import java.io.Reader;

import de.uka.ilkd.asmkey.parser.ast.*;
import de.uka.ilkd.key.parser.ParserException;


/** This class contains static methods for parsing terms with the
 *  generated (antlr) parser. It allows parsing of terms, ASM rules
 *  and problem files. The methods return abstract syntax tree, that
 *  represent the context * free structure of the grammer. The
 *  analysis of static semantic (like variable binding and types) is
 *  not done.
 * 
 * @see AbstractAstParsitor
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public final class AstParser {

    /** The used AstFactory. */
    private static final AstFactory af = new AstFactoryImpl();


    /** Parse term. */
    public static AstTerm parseTerm(Reader reader) throws ParserException {
	AbstractAstParsitor parsitor = new AbstractAstParsitor(reader, af) {
		protected Object internParse()
		    throws antlr.TokenStreamException, antlr.RecognitionException
		{
		    return parser.top_term();
		}
	    };
	return (AstTerm) parsitor.parse();
    }

    /** Parse ASM rule. */
    public static AstAsmRule parseAsmRule(Reader reader) throws ParserException {
	AbstractAstParsitor parsitor = new AbstractAstParsitor(reader, af) {
		protected Object internParse() 
		    throws antlr.TokenStreamException, antlr.RecognitionException
		{
		    return parser.top_asm_rule();
		}
	    };
	return (AstAsmRule) parsitor.parse();
    }

    /** Parse ASM unit. */
    public static AstUnit parseUnit(File file) throws ParserException, FileNotFoundException {
	AbstractAstParsitor parsitor = new AbstractAstParsitor(file, af) {
		protected Object internParse() 
		    throws antlr.TokenStreamException, antlr.RecognitionException
		{
		    return parser.top_unit();
		}
	    };
	return (AstUnit) parsitor.parse();
    }

    /** Parse proof file */
    public static AstProof parseProof(File file) throws ParserException, FileNotFoundException {
	AbstractAstParsitor parsitor = new AbstractAstParsitor(file, af) {
		protected Object internParse()
		    throws antlr.TokenStreamException, antlr.RecognitionException {
		    return parser.top_proof();
		}
	    };
	return (AstProof) parsitor.parse();
    }

}
