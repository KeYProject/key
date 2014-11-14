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

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;

import org.antlr.runtime.ANTLRReaderStream;
import org.antlr.runtime.ANTLRStringStream;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.util.KeYExceptionHandler;

/*
 * Extends generated class {@link KeYLexer} with custom constructors.
 */
public class KeYLexerF extends KeYLexer {
    public KeYLexerF(InputStream file, String fileName, KeYExceptionHandler keh) throws IOException {
        this(new InputStreamReader(file, Main.DEFAULT_CHARSET), fileName, keh);
    }

    public KeYLexerF(Reader file, String fileName, KeYExceptionHandler keh)
            throws IOException {
        super(getStream(new ANTLRReaderStream(file), fileName), keh);
    }

    public KeYLexerF(String file, String fileName, KeYExceptionHandler keh) {
        super(getStream(new ANTLRStringStream(file), fileName), keh);
    }

    /*
     * Use this to set stream name before sending it to super constructor.
     */
    static ANTLRStringStream getStream(ANTLRStringStream stream, String fileName) {
        stream.name = fileName;
        return stream;
    }

}
