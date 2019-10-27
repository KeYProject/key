package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jetbrains.annotations.NotNull;

import java.io.IOException;
import java.net.URL;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.stream.Collectors;

import static de.uka.ilkd.key.nparser.ParsingFacade.parseFiles;

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

    public KeyIO(Services services, NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }

    public KeyIO(Services services) {
        this(services, services.getNamespaces());
    }

    public KeyIO() {
        this(new Services(new JavaProfile()));
    }


    /* base path needed
    public ParsedKeyFile parseProblemFile(CharStream stream) {
        var ctx = ParsingFacade.parseFile(stream);
        return (ParsedKeyFile) visit(ctx);
    }*/

    private <T> T visit(@NotNull ParserRuleContext ctx) {
        FileVisitor b = new FileVisitor(services, nss, new ParsedKeyFile());
        return (T) ctx.accept(b);
    }

    public ParsedKeyFile parseProblemFile(@NotNull URL file) throws IOException {
        long start =System.currentTimeMillis();
        var seq = new ArrayList<>(parseFiles(file));
        long stop =System.currentTimeMillis();
        System.err.format("MODE: %s took %d%n", "PARSING", stop-start);

        ParsedKeyFile pkf = new ParsedKeyFile();
        var parsers = seq.stream().map(it -> new FileVisitor(services, nss, pkf))
                .collect(Collectors.toList());
        Collections.reverse(seq);
        for (var mode : FileVisitor.Mode.values()) {
            start =System.currentTimeMillis();
            for (int i = 0; i < seq.size(); i++) {
                KeYParser.FileContext s = seq.get(i);
                var p = parsers.get(i);
                p.setMode(mode);
                s.accept(p);
            }
            stop=System.currentTimeMillis();
            System.err.format("MODE: %s took %d%n", mode, stop-start);
        }
        return pkf;
    }

    public ParsedKeyFile parseProblemFile(@NotNull Path file) throws IOException {
        return parseProblemFile(file.toUri().toURL());
    }


    public @NotNull Term parseExpression(@NotNull String expr) {
        return parseExpression(CharStreams.fromString(expr));
    }

    public Term parseExpression(CharStream stream) {
        var ctx = ParsingFacade.parseExpression(stream);
        return (Term) visit(ctx);
    }

    public Services getServices() {
        return services;
    }
}
