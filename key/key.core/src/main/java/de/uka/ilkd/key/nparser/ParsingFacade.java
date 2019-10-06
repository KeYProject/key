package de.uka.ilkd.key.nparser;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;

/**
 * @author Alexander Weigl
 * @version 1 (19.08.19)
 */
public abstract class ParsingFacade {
    public static KeYParser.FileContext parseFile(Path file) throws IOException {
        return parseFile(CharStreams.fromPath(file));
    }

    public static KeYParser.FileContext parseFile(File file) throws IOException {
        return parseFile(file.toPath());
    }

    public static KeYParser.FileContext parseFile(CharStream stream) {
        var p = createParser(stream);
        KeYParser.FileContext ctx = p.file();
        return ctx;
    }

    public static KeYParser.TermContext parseExpression(CharStream stream) {
        var p = createParser(stream);
        return p.term();
    }

    private static KeYParser createParser(CharStream stream) {
        var p = new KeYParser(new CommonTokenStream(lex(stream)));
        //p.removeErrorListeners();
        //TODO exception throwingp.addErrorListener();
        return p;
    }

    public static KeYLexer lex(Path file) throws IOException {
        return lex(CharStreams.fromPath(file));
    }

    public static KeYLexer lex(CharStream stream) {
        return new KeYLexer(stream);
    }
}
