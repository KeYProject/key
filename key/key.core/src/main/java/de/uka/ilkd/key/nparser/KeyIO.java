package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Position;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.jetbrains.annotations.NotNull;

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
    private URL resource;
    private List<KeYParser.FileContext> ctx = new LinkedList<>();

    public KeyIO(URL file, Services services, NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
        this.resource = file;
    }

    public KeyIO(URL file, Services services) {
        this(file, services, services.getNamespaces());
    }

    public KeyIO(URL file) {
        this(file, new Services(new JavaProfile()));
    }

    public void parseFile() throws IOException {
        long start = System.currentTimeMillis();
        ctx = parseFiles(resource);
        long stop = System.currentTimeMillis();
        System.err.format("Parsing took %d%n", stop - start);
    }

    public ProblemInformation getProblemInformation() {
        if (ctx.isEmpty()) {
            throw new IllegalStateException("No files loaded.");
        }
        return ParsingFacade.getProblemInformation(ctx.get(0));
    }

    public Map<String, Set<String>> loadChoices() {
        if (ctx.isEmpty()) {
            throw new IllegalStateException("No files loaded.");
        }
        return ParsingFacade.getChoices(ctx);
    }

    public void loadDeclarations() {
        var declBuilder = new DeclarationBuilder(services, nss);
        long start = System.currentTimeMillis();
        for (int i = ctx.size() - 1; i >= 0; i--) { // process backwards
            KeYParser.FileContext s = ctx.get(i);
            //var p = parsers.get(i);
            s.accept(declBuilder);
        }
        long stop = System.currentTimeMillis();
        System.err.format("MODE: %s took %d%n", "declarations", stop - start);
    }

    public void loadSndDegreeDeclarations() {
        var visitor = new FunctionPredicateBuilder(services, nss);
        long start = System.currentTimeMillis();
        for (int i = ctx.size()-1; i >=0 ; --i) {
            KeYParser.FileContext s = ctx.get(i);
            s.accept(visitor);
        }
        long stop = System.currentTimeMillis();
        System.err.format("MODE: %s took %d%n", "2nd degree decls", stop - start);
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
            KeYParser.FileContext s = ctx.get(i);
            var p = parsers.get(i);
            s.accept(p);
            taclets.addAll(p.getTaclets());
        }
        long stop = System.currentTimeMillis();
        System.err.format("MODE: %s took %d%n", "taclets", stop - start);
        return taclets;
    }

    public @NotNull Term parseExpression(@NotNull String expr) {
        return parseExpression(CharStreams.fromString(expr));
    }

    public Term parseExpression(CharStream stream) {
        var ctx = ParsingFacade.parseExpression(stream);
        return (Term) ctx.accept(new ExpressionBuilder(services, nss));
    }

    public Services getServices() {
        return services;
    }

    public List<Taclet> loadComplete() throws IOException {
        if (ctx.isEmpty()) parseFile();
        loadDeclarations();
        loadSndDegreeDeclarations();
        return loadTaclets();
    }

    public KeyIO load(Path file) {
        try {
            resource = file.toUri().toURL();
            ctx.clear();
        } catch (MalformedURLException e) {
            e.printStackTrace();
        }
        return this;
    }

    public ProblemFinder loadCompleteProblem() throws IOException {
        if (ctx.isEmpty()) parseFile();
        loadDeclarations();
        loadSndDegreeDeclarations();
        loadTaclets();
        return loadProblem();
    }
}
