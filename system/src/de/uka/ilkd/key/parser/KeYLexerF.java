package de.uka.ilkd.key.parser;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;

import antlr.CharScanner;
import antlr.Token;
import antlr.TokenStreamException;

import de.uka.ilkd.key.util.KeYExceptionHandler;

public class KeYLexerF extends CharScanner {

    private KeYLexer keYLexer;

    public KeYLexerF(InputStream in, KeYExceptionHandler keh)
	    throws FileNotFoundException {
	try {
	    this.keYLexer = new KeYLexer(in, keh);
	} catch (IOException e) {
	    throw new FileNotFoundException(e.getMessage());
	}
    }

    public KeYLexerF(Reader in, KeYExceptionHandler keh)
	    throws FileNotFoundException {
	try {
	    this.keYLexer = new KeYLexer(in, keh);
	} catch (IOException e) {
	    throw new FileNotFoundException(e.getMessage());
	}
    }

    public KeYLexerF(String in, KeYExceptionHandler keh) {
	this.keYLexer = new KeYLexer(in, keh);
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
