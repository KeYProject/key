package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;

import static de.uka.ilkd.key.nparser.ParsingFacade.parseFile;

/**
 * This facade provides high level access to parse and
 * interpret key files (declarations, proof, problem) or input string like terms.
 *
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class KeyIO {
    private final Services services;
    private final NamespaceSet nss;

    @Contract(pure = true)
    public KeyIO(Services services, NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }

    public Object parseFileAndVisit(CharStream stream) {
        var ctx = ParsingFacade.parseFile(stream);
        return visit(ctx);
    }

    public Term parseTermAndVisit(CharStream stream) {
        var ctx = ParsingFacade.parseExpression(stream);
        return (Term) visit(ctx);
    }

    private Object visit(@NotNull ParserRuleContext ctx) {
        Builder b = new Builder(null, services, nss);
        return ctx.accept(b);
    }

    public Object parseProblemFile(@NotNull File file) throws IOException {
        return parseFile(file.toPath());
    }

    public Object parseProblemFile(@NotNull Path file) throws IOException {
        return parseFileAndVisit(CharStreams.fromPath(file));
    }

    public @NotNull Term parseExpression(@NotNull String expr) {
        return parseTermAndVisit(CharStreams.fromString(expr));
    }
}
