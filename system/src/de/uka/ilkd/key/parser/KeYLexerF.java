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

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.ANTLRReaderStream;
import org.antlr.runtime.ANTLRStringStream;

import antlr.CharScanner;
import antlr.Token;
import antlr.TokenStreamException;

import de.uka.ilkd.key.util.KeYExceptionHandler;

public class KeYLexerF extends CharScanner {

    private KeYLexer keYLexer;

    public KeYLexerF(InputStream file, String filename, KeYExceptionHandler keh)
	    throws FileNotFoundException {
	try {
	    final ANTLRInputStream stream = new ANTLRInputStream(file);
	    stream.name = filename;
	    this.keYLexer = new KeYLexer(stream, keh);
	} catch (IOException e) {
	    throw new FileNotFoundException(e.getMessage());
	}
    }

    public KeYLexerF(Reader file, String filename, KeYExceptionHandler keh)
	    throws FileNotFoundException {
	try {
	    final ANTLRReaderStream stream = new ANTLRReaderStream(file);
	    stream.name = filename;
	    this.keYLexer = new KeYLexer(stream, keh);
	} catch (IOException e) {
	    throw new FileNotFoundException(e.getMessage());
	}
    }

    public KeYLexerF(String file, String filename, KeYExceptionHandler keh) {
	final ANTLRStringStream stream = new ANTLRStringStream(file);
	stream.name = filename;
	this.keYLexer = new KeYLexer(stream, keh);
    }

    public KeYLexer getKeYLexer() {
	return this.keYLexer;
    }

    @Override
    public Token nextToken() throws TokenStreamException {
	org.antlr.runtime.Token token = this.keYLexer.nextToken();

	return new Token(token.getType(), token.getText());
    }
}