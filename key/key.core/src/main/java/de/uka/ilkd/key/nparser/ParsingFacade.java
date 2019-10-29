package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.io.RuleSource;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.channels.ReadableByteChannel;
import java.nio.charset.Charset;
import java.nio.charset.CodingErrorAction;
import java.nio.file.Path;
import java.util.*;

/**
 * This facade provides low-level access to the ANTLR4 Parser and Lexer.
 * <p>
 * You should only use it if you need access to the parse trees instead of terms or taclet structure.
 *
 * @author Alexander Weigl
 * @version 1 (19.08.19)
 */
public abstract class ParsingFacade {
    public static List<KeYParser.FileContext> parseFiles(URL url) throws IOException {
        List<KeYParser.FileContext> ctxs = new LinkedList<>();
        Stack<URL> queue = new Stack<>();
        queue.add(url);
        Set<URL> reached = new HashSet<>();

        while (!queue.isEmpty()) {
            url = queue.pop();
            reached.add(url);
            var ctx = parseFile(url);
            ctxs.add(ctx);
            var includes = getIncludes(url, ctx).getRuleSets();
            for (RuleSource u : includes) {
                if (!reached.contains(u.url())) {
                    queue.add(u.url());
                }
            }
        }
        return ctxs;
    }

    public static Includes getIncludes(URL base, KeYParser.FileContext ctx) {
        var finder = new IncludeFinder(base);
        ctx.accept(finder);
        return finder.getIncludes();
    }

    public static Map<String, Set<String>> getChoices(List<KeYParser.FileContext> ctxs) {
        var finder = new ChoiceFinder();
        ctxs.forEach(it -> it.accept(finder));
        return finder.getChoices();
    }

    public static ProblemInformation getProblemInformation(KeYParser.FileContext ctx) {
        FindProblemInformation fpi = new FindProblemInformation();
        ctx.accept(fpi);
        return fpi.getProblemInformation();
    }

    public static KeYParser.FileContext parseFile(URL url) throws IOException {
        long start = System.currentTimeMillis();
        try (BufferedInputStream is = new BufferedInputStream(url.openStream());
             ReadableByteChannel channel = Channels.newChannel(is)) {
            var stream = CharStreams.fromChannel(
                    channel,
                    Charset.defaultCharset(),
                    4096,
                    CodingErrorAction.REPLACE,
                    url.toString(),
                    -1);
            return parseFile(stream);
        } finally {
            long stop = System.currentTimeMillis();
            System.err.printf("PARSING %s took %d ms\n", url, stop - start);
        }
    }

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
        //TODO exception throwing
        p.addErrorListener(p.getErrorReporter());
        return p;
    }

    public static KeYLexer lex(Path file) throws IOException {
        return lex(CharStreams.fromPath(file));
    }

    public static KeYLexer lex(CharStream stream) {
        return new KeYLexer(stream);
    }
}
