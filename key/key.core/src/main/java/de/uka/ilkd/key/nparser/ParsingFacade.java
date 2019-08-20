package de.uka.ilkd.key.nparser;

import org.antlr.v4.runtime.*;
/**
 * @author Alexander Weigl
 * @version 1 (19.08.19)
 */
public abstract class ParsingFacade {
    public KeYParser.FileContext parseFile(org.antlr.v4.runtime.CharStream stream) {
        var p = createParser(stream);
        KeYParser.FileContext ctx = p.file();
        return ctx;
    }

    private KeYParser createParser(CharStream stream) {
        return new KeYParser(new CommonTokenStream(new KeYLexer(stream)));
    }
}
