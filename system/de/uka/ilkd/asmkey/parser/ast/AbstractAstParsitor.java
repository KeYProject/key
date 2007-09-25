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

import java.io.File;
import java.io.FileNotFoundException;
import java.io.Reader;

import de.uka.ilkd.asmkey.parser.antlr.AsmKeyLexer;
import de.uka.ilkd.asmkey.parser.antlr.AsmKeyParser;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;

public abstract class AbstractAstParsitor {

    protected AsmKeyParser parser;
    protected AsmKeyLexer lexer;

    private AbstractAstParsitor(AsmKeyLexer lexer, AstFactory factory) {
	this.parser = new AsmKeyParser(lexer, factory);
	this.lexer = lexer;
    }

    public AbstractAstParsitor(Reader in, AstFactory af) {
	this(new AsmKeyLexer(in), af);
    }
    
    public AbstractAstParsitor(File file, AstFactory af) throws FileNotFoundException {
	this(new AsmKeyLexer(file), af);
    }


    /**
     * subclasses must implement this method, that does the actual parsing 
     * typically, they will invoke the "right" method of the AsmKeyParser parser.
     */
    abstract protected Object internParse()
	throws ParserException, antlr.TokenStreamException, antlr.RecognitionException;

    /**
     * parsing and standart treatment of the antlr exception.
     */
    public Object parse() throws ParserException {
	try {
	    return internParse();
	} catch (antlr.TokenStreamException tse) {
	    throw new ParserException(tse.getMessage(), null);
	} catch (antlr.RecognitionException re) {
	    throw new ParserException
		(re.getMessage(), new Location(re.getFilename(), re.getLine(), re.getColumn()));
	}
	finally {
	    lexer.close(); 
	}
    }

    
    
}
