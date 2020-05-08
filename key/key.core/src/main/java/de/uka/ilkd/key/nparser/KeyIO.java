package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.builder.*;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.Taclet;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

import static de.uka.ilkd.key.nparser.ParsingFacade.parseFiles;

/**
 * This facade provides high level access to parse and
 * interpret key files or input strings into declarations, proof, problem, terms.
 * <p>
 * This classes encapsulates the {@link Services}, {@link NamespaceSet} for {@link SchemaVariable}s.
 * <b>It also modifies them during interpretation.</b>
 *
 * @author Alexander Weigl
 * @version 1 (17.10.19)
 */
public class KeyIO {
    private final Services services;
    private final NamespaceSet nss;
    private @Nullable Namespace<SchemaVariable> schemaNamespace;
    private @Nullable List<BuildingIssue> warnings;

    public KeyIO(@NotNull Services services, @NotNull NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }

    public KeyIO(Services services) {
        this(services, services.getNamespaces());
    }

    public KeyIO() {
        this(new Services(new JavaProfile()));
    }


    /**
     * Given an input string, this function returns a term if parsable.
     *
     * @param expr a valid stream
     * @return a valid term
     * @throws BuildingException if an unrecoverable error during construction or parsing happened
     */
    public @NotNull Term parseExpression(@NotNull String expr) {
        return parseExpression(CharStreams.fromString(expr));
    }

    /**
     * Given an input stream, this function returns an term if parsable.
     *
     * @param stream a valid stream
     * @return a valid term
     * @throws BuildingException if an unrecoverable error during construction or parsing happened
     */
    public @NotNull Term parseExpression(@NotNull CharStream stream) {
        KeyAst.Term ctx = ParsingFacade.parseExpression(stream);
        ExpressionBuilder visitor = new ExpressionBuilder(services, nss);
        if (schemaNamespace != null)
            visitor.setSchemaVariables(schemaNamespace);
        Term t = (Term) ctx.accept(visitor);
        warnings = visitor.getBuildingIssues();
        return t;
    }


    /**
     * Given an input stream, this function returns a sequent if parsable.
     *
     * @param stream a valid stream
     * @return a valid sequent
     * @throws BuildingException if an unrecoverable error during construction or parsing happened
     */
    public @NotNull Sequent parseSequence(@NotNull CharStream stream) {
        KeyAst.Seq ctx = ParsingFacade.parseSequent(stream);
        ExpressionBuilder visitor = new ExpressionBuilder(services, nss);
        if (schemaNamespace != null)
            visitor.setSchemaVariables(schemaNamespace);
        Sequent seq = (Sequent) ctx.accept(visitor);
        warnings = visitor.getBuildingIssues();
        return seq;
    }

    public Services getServices() {
        return services;
    }

    /**
     * Create a loader instance for the given path.
     *
     * @param file
     * @return
     */
    public Loader load(Path file) {
        try {
            return new Loader(file.toUri().toURL());
        } catch (MalformedURLException e) {
            throw new RuntimeException(e);
        }
    }


    public Loader load(CharStream content) {
        return new Loader(content, null);
    }

    public Loader load(String content) {
        return load(CharStreams.fromString(content));
    }


    /**
     * Create a loader instance for the given path.
     *
     * @param u
     * @return
     */
    public Loader load(URL u) {
        return new Loader(u);
    }


    /**
     * @param ctx
     * @return
     */
    public List<Taclet> findTaclets(KeyAst.File ctx) {
        TacletPBuilder visitor = new TacletPBuilder(services, nss);
        ctx.accept(visitor);
        return visitor.getTopLevelTaclets();
    }

    /**
     * @param ctx
     */
    public void evalDeclarations(KeyAst.File ctx) {
        DeclarationBuilder declBuilder = new DeclarationBuilder(services, nss);
        ctx.accept(declBuilder);
    }

    /**
     * @param ctx
     */
    public void evalFuncAndPred(KeyAst.File ctx) {
        FunctionPredicateBuilder visitor = new FunctionPredicateBuilder(services, nss);
        ctx.accept(visitor);
    }


    public void setSchemaNamespace(Namespace<SchemaVariable> ns) {
        schemaNamespace = ns;
    }

    /**
     * Loading of complete KeY files into the given schema.
     * Supports recursive loading, but does not provide support for Java and Java type informations.
     * <p>
     * Little sister of {@link de.uka.ilkd.key.proof.init.ProblemInitializer}.
     */
    public class Loader {
        private final URL resource;
        private final CharStream content;
        private List<KeyAst.File> ctx = new LinkedList<>();
        private Namespace<SchemaVariable> schemaNamespace;

        Loader(URL resource) {
            this(null, resource);
        }

        Loader(CharStream content, URL url) {
            resource = url;
            this.content = content;
        }

        public Namespace<SchemaVariable> getSchemaNamespace() {
            return schemaNamespace;
        }

        public List<Taclet> loadComplete() throws IOException {
            if (ctx.isEmpty()) parseFile();
            loadDeclarations();
            loadSndDegreeDeclarations();
            return loadTaclets();
        }

        public ProblemFinder loadCompleteProblem() throws IOException {
            if (ctx.isEmpty()) parseFile();
            loadDeclarations();
            loadSndDegreeDeclarations();
            loadTaclets();
            return loadProblem();
        }

        public Loader parseFile() throws IOException {
            if (!ctx.isEmpty()) return this;
            //long start = System.currentTimeMillis();
            if (resource != null)
                ctx = parseFiles(resource);
            else {
                KeyAst.File c = ParsingFacade.parseFile(content);
                ctx.add(c);
            }
            //long stop = System.currentTimeMillis();
            //System.err.format("Parsing took %d%n", stop - start);
            return this;
        }

        public ProblemInformation getProblemInformation() {
            if (ctx.isEmpty()) {
                throw new IllegalStateException("No files loaded.");
            }
            return ctx.get(0).getProblemInformation();
        }

        public ChoiceInformation loadChoices() {
            if (ctx.isEmpty()) {
                throw new IllegalStateException("No files loaded.");
            }
            return ParsingFacade.getChoices(ctx);
        }

        public Loader loadDeclarations() {
            //var choiceFinder = new ChoiceFinder(nss.choices());
            DeclarationBuilder declBuilder = new DeclarationBuilder(services, nss);
            long start = System.currentTimeMillis();
            for (int i = ctx.size() - 1; i >= 0; i--) { // process backwards
                KeyAst.File s = ctx.get(i);
                //var p = parsers.get(i);
                //s.accept(choiceFinder);
                s.accept(declBuilder);
            }
            long stop = System.currentTimeMillis();
            //System.err.format("MODE: %s took %d%n", "declarations", stop - start);
            return this;
        }

        public Loader loadSndDegreeDeclarations() {
            FunctionPredicateBuilder visitor = new FunctionPredicateBuilder(services, nss);
            long start = System.currentTimeMillis();
            for (int i = ctx.size() - 1; i >= 0; --i) {
                KeyAst.File s = ctx.get(i);
                s.accept(visitor);
            }
            long stop = System.currentTimeMillis();
            //System.err.format("MODE: %s took %d%n", "2nd degree decls", stop - start);
            return this;
        }

        public ProblemFinder loadProblem() {
            if (ctx.isEmpty()) throw new IllegalStateException();
            ProblemFinder pf = new ProblemFinder(services, nss);
            ctx.get(0).accept(pf);
            return pf;
        }

        public List<Taclet> loadTaclets() {
            if (ctx.isEmpty()) throw new IllegalStateException();
            List<TacletPBuilder> parsers = ctx.stream().map(it -> new TacletPBuilder(services, nss))
                    .collect(Collectors.toList());
            //Collections.reverse(parsers);
            long start = System.currentTimeMillis();
            List<Taclet> taclets = new ArrayList<>(2048);
            for (int i = 0; i < ctx.size(); i++) {
                KeyAst.File s = ctx.get(i);
                TacletPBuilder p = parsers.get(i);
                if (KeyIO.this.schemaNamespace != null) {
                    p.setSchemaVariables(new Namespace<>(KeyIO.this.schemaNamespace));
                }
                s.accept(p);
                taclets.addAll(p.getTopLevelTaclets());
                schemaNamespace = p.schemaVariables();
            }
            long stop = System.currentTimeMillis();
            //System.err.format("MODE: %s took %d%n", "taclets", stop - start);
            return taclets;
        }

        public Term getProblem() {
            //TODO
            return null;
        }
    }
}
