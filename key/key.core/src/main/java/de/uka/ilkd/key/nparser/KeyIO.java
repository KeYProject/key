package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Position;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.Path;
import java.util.*;
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

    public static @Nullable String findJavaPath(KeyAst.File ctx) {
        final String[] javaPath = {null};
        ctx.accept(new AbstractBuilder<Void>() {
            @Override
            public Void visitOneJavaSource(KeYParser.OneJavaSourceContext ctx) {
                javaPath[0] = ctx.getText();
                return null;
            }
        });
        return javaPath[0];
    }

    public static @Nullable String findBootClassPath(KeyAst.File ctx) {
        BootClasspathFinder psf = new BootClasspathFinder();
        ctx.accept(psf);
        return psf.getBootClasspath();
    }

    public static Set<Choice> findActivatedChoices(KeyAst.File ctx, Namespace<Choice> ns) {
        ChoiceFinder cf = new ChoiceFinder(ns);
        ctx.accept(cf);
        return cf.getChoiceInformation().getActivatedChoices();
    }

    public @NotNull Term parseExpression(@NotNull String expr) {
        return parseExpression(CharStreams.fromString(expr));
    }

    public Term parseExpression(CharStream stream) {
        var ctx = ParsingFacade.parseExpression(stream);
        return (Term) ctx.accept(new ExpressionBuilder(services, nss));
    }

    public Sequent parseSequence(CharStream stream) {
        var ctx = ParsingFacade.parseSequent(stream);
        ExpressionBuilder visitor = new ExpressionBuilder(services, nss);
        var seq = (Sequent) ctx.accept(visitor);
        if (visitor.getWarnings().isEmpty()) {
            return seq;
        }
        throw new BuildingExceptions(visitor.getWarnings());
    }

    public Services getServices() {
        return services;
    }

    public Loader load(Path file) {
        try {
            return new Loader(file.toUri().toURL());
        } catch (MalformedURLException e) {
            throw new RuntimeException(e);
        }
    }

    public Loader load(URL u) {
        return new Loader(u);
    }

    public List<Taclet> findTaclets(KeyAst.File ctx) {
        var visitor = new TacletPBuilder(services, nss);
        ctx.accept(visitor);
        return visitor.getTaclets();
    }

    /*
    public List<Contract> findContracts(KeyAst.File ctx) {
        ProblemFinder pf = new ProblemFinder(services, nss);
        ctx.accept(pf);
        return pf.getContracts();
    }*/

    public void evalDeclarations(KeyAst.File ctx) {
        var declBuilder = new DeclarationBuilder(services, nss);
        ctx.accept(declBuilder);
    }

    public void evalFuncAndPred(KeyAst.File ctx) {
        var visitor = new FunctionPredicateBuilder(services, nss);
        ctx.accept(visitor);
    }

    public Loader load(String content) {
        return new Loader(content, null);
    }

    public class Loader {
        private final URL resource;
        private final String content;
        private List<KeyAst.File> ctx = new LinkedList<>();

        Loader(URL resource) {
            this(null, resource);
        }

        public Loader(String content, URL url) {
            resource = url;
            this.content = content;
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
            //long start = System.currentTimeMillis();
            if(resource!=null)
                ctx = parseFiles(resource);
            else{
                var c = ParsingFacade.parseFile(CharStreams.fromString(content));
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
            var declBuilder = new DeclarationBuilder(services, nss);
            long start = System.currentTimeMillis();
            for (int i = ctx.size() - 1; i >= 0; i--) { // process backwards
                KeyAst.File s = ctx.get(i);
                //var p = parsers.get(i);
                s.accept(declBuilder);
            }
            long stop = System.currentTimeMillis();
            System.err.format("MODE: %s took %d%n", "declarations", stop - start);
            return this;
        }

        public Loader loadSndDegreeDeclarations() {
            var visitor = new FunctionPredicateBuilder(services, nss);
            long start = System.currentTimeMillis();
            for (int i = ctx.size() - 1; i >= 0; --i) {
                KeyAst.File s = ctx.get(i);
                s.accept(visitor);
            }
            long stop = System.currentTimeMillis();
            System.err.format("MODE: %s took %d%n", "2nd degree decls", stop - start);
            return this;
        }

        public Pair<String, Position> getProofScript() {
            if (ctx.isEmpty()) {
                throw new IllegalStateException("No files loaded.");
            }
            ProofScriptFinder psf = new ProofScriptFinder();
            return new Pair<>(psf.getProofScript(), psf.getPosition());
        }

        public ProblemFinder loadProblem() {
            if (ctx.isEmpty()) throw new IllegalStateException();
            ProblemFinder pf = new ProblemFinder(services, nss);
            ctx.get(0).accept(pf);
            return pf;
        }

        public List<Taclet> loadTaclets() {
            var parsers = ctx.stream().map(it -> new TacletPBuilder(services, nss))
                    .collect(Collectors.toList());
            //Collections.reverse(parsers);
            long start = System.currentTimeMillis();
            List<Taclet> taclets = new ArrayList<>(2048);
            for (int i = 0; i < ctx.size(); i++) {
                KeyAst.File s = ctx.get(i);
                var p = parsers.get(i);
                s.accept(p);
                taclets.addAll(p.getTaclets());
            }
            long stop = System.currentTimeMillis();
            System.err.format("MODE: %s took %d%n", "taclets", stop - start);
            return taclets;
        }

        public Term getProblem() {
            //TODO
            return null;
        }
    }
}
