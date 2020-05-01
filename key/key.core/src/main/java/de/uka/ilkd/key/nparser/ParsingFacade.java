package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.nparser.builder.ChoiceFinder;
import de.uka.ilkd.key.proof.io.RuleSource;
import org.antlr.v4.runtime.*;
import org.jetbrains.annotations.NotNull;

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
    /**
     * Use this function to retrieve the {@link ParserRuleContext} inside and {@link KeyAst} object.
     * <b>The use of this is discourage and should be avoided in all high level scenarios.</b>
     *
     * @param ast
     * @param <T>
     * @return
     */
    public static <T extends ParserRuleContext> @NotNull T getParseRuleContext(@NotNull KeyAst<T> ast) {
        return ast.ctx;
    }

    public static List<KeyAst.File> parseFiles(URL url) throws IOException {
        List<KeyAst.File> ctxs = new LinkedList<>();
        Stack<URL> queue = new Stack<>();
        queue.add(url);
        Set<URL> reached = new HashSet<>();

        while (!queue.isEmpty()) {
            url = queue.pop();
            reached.add(url);
            KeyAst.File ctx = parseFile(url);
            ctxs.add(ctx);
            Collection<RuleSource> includes = ctx.getIncludes(url).getRuleSets();
            for (RuleSource u : includes) {
                if (!reached.contains(u.url())) {
                    queue.add(u.url());
                }
            }
        }
        return ctxs;
    }

    public static ChoiceInformation getChoices(List<KeyAst.File> ctxs) {
        ChoiceInformation ci = new ChoiceInformation();
        ChoiceFinder finder = new ChoiceFinder(ci);
        ctxs.forEach(it -> it.accept(finder));
        return ci;
    }

    private static KeYParser createParser(CharStream stream) {
        KeYParser p = new KeYParser(new CommonTokenStream(lex(stream)));
        p.removeErrorListeners();
        p.addErrorListener(p.getErrorReporter());
        return p;
    }

    public static KeYLexer lex(Path file) throws IOException {
        return lex(CharStreams.fromPath(file));
    }

    public static KeYLexer lex(CharStream stream) {
        return new KeYLexer(stream);
    }

    public static KeyAst.File parseFile(URL url) throws IOException {
        long start = System.currentTimeMillis();
        try (BufferedInputStream is = new BufferedInputStream(url.openStream());
             ReadableByteChannel channel = Channels.newChannel(is)) {
            CodePointCharStream stream = CharStreams.fromChannel(
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

    public static KeyAst.File parseFile(Path file) throws IOException {
        return parseFile(CharStreams.fromPath(file));
    }

    public static KeyAst.File parseFile(File file) throws IOException {
        return parseFile(file.toPath());
    }

    public static KeyAst.File parseFile(CharStream stream) {
        KeYParser p = createParser(stream);
        KeYParser.FileContext ctx = p.file();
        return new KeyAst.File(ctx);
    }

    public static KeyAst.Term parseExpression(CharStream stream) {
        KeYParser p = createParser(stream);
        KeYParser.TermContext term = p.termEOF().term();
        p.getErrorReporter().throwException();
        return new KeyAst.Term(term);
    }

    public static KeyAst.Seq parseSequent(CharStream stream) {
        KeYParser p = createParser(stream);
        return new KeyAst.Seq(p.seqEOF().seq());
    }

    public static String getValue(KeYParser.String_valueContext ctx) {
        return ctx.getText().substring(1, ctx.getText().length() - 1);
    }

    public static KeYParser.Id_declarationContext parseIdDeclaration(CharStream stream) {
        KeYParser p = createParser(stream);
        return p.id_declaration();
        /*
    @Override
    public IdDeclaration visitId_declaration(KeYParser.Id_declarationContext ctx) {
        var id = (String) ctx.IDENT().getText();
        var s = (Sort) (ctx.sortId_check() != null ? accept(ctx.sortId_check()) : null);
        return new IdDeclaration(id, s);
    }
    */
    }
}
