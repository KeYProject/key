package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.net.URL;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Properties;
import java.util.Set;

import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.BOOL;
import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.UNIVERSE;

public class DefinedSymbolsHandler implements SMTHandler {

    public final static String PREFIX = "k_";

    private final static Set<String> SUPPORTED_SUFFIXES =
            new HashSet<>(Arrays.asList(".axioms", ".dl", ".taclets"));

    private static final String PATTERN_NAME = "__P__";

    private final Set<String> supportedFunctions = new HashSet<>();
    private Services services;

    @Override
    public void init(MasterHandler masterHandler, Services services) throws IOException {

        this.services = services.copy(true);
        this.services.getNamespaces().functions().add(PatternHandler.FORMULA_PATTERN_FUNCTION);
        this.services.getNamespaces().functions().add(PatternHandler.PATTERN_FUNCTION);

        String resourceName = getClass().getSimpleName() + ".preamble.xml";
        URL url = getClass().getResource(resourceName);
        if (url == null) {
            throw new IOException("Preamble for defined functions does not exist. Rerun gradle to build it.");
        }

        Properties props = new Properties();
        try (InputStream is = url.openStream()) {
            props.loadFromXML(is);
        }

        for (String prop : props.stringPropertyNames()) {
            int dot = prop.lastIndexOf('.');
            if (dot < 0) {
                continue;
            }
            String ext = prop.substring(dot);
            if (SUPPORTED_SUFFIXES.contains(ext)) {
                String fct = prop.substring(0, dot);
                supportedFunctions.add(fct);
            }
        }

        masterHandler.registerSnippets(props);
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        return op instanceof Function && supportedFunctions.contains(op.name().toString());
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortedOperator op = (SortedOperator) term.op();
        String name = op.name().toString();
        String prefixedname = PREFIX + name;

        List<SExpr> children = trans.translate(term.subs(), Type.UNIVERSE);
        SExpr.Type exprType = term.sort() == Sort.FORMULA ? BOOL : UNIVERSE;
        SExpr result = new SExpr(prefixedname, exprType, children);

        if(trans.isKnownSymbol(name)) {
            return result;
        }

        Writable decls = trans.getSnippet(name + ".decls", HandlerUtil.funDeclaration(op, prefixedname));
        trans.addDeclaration(decls);

        if (op.sort() != Sort.FORMULA) {
            Writable typing = trans.getSnippet(name + ".typing", HandlerUtil.funTypeAxiom(op, prefixedname, trans));
            trans.addAxiom(typing);
        }

        trans.addKnownSymbol(name);

        if (trans.hasSnippet(name + ".axioms")) {
            handleSMTAxioms(trans, name);
            return result;
        }

        if (trans.hasSnippet(name + ".dl")) {
            handleDLAxioms(name, trans);
            return result;
        }

        if (trans.hasSnippet(name + ".taclets")) {
            // handle taclets
            handleTacletAxioms(name, trans);
            return result;
        }

        throw new SMTTranslationException("I thought I would handle this term, but cannot: " + term);

    }

    private void handleTacletAxioms(String name, MasterHandler trans) {
        String taclets = trans.getSnippet(name + ".taclets");
        throw new Error("not supported yet");
    }

    private void handleSMTAxioms(MasterHandler trans, String name) {
        // well ... if that is defined by axioms use the general purpose mechanism.
        String axioms = trans.getSnippet(name + ".axioms");
        trans.addAxiom(new VerbatimSMT(axioms));
        String[] deps = trans.getSnippet(name + ".deps", "").trim().split(", *");
        for (String dep : deps) {
            trans.addFromSnippets(dep);
        }
    }

    private void handleDLAxioms(String name, MasterHandler trans) throws SMTTranslationException {
        int cnt = 2;
        String snipName = name + ".dl";
        String dl = trans.getSnippet(snipName);
        do {
            DefaultTermParser tp = new DefaultTermParser();
            try {
                Term axiom = tp.parse(new StringReader(dl), Sort.FORMULA, services,
                        services.getNamespaces(), new AbbrevMap());
                trans.addAxiom(SExprs.assertion(trans.translate(axiom)));
            } catch (ParserException e) {
                throw new SMTTranslationException("Error while translating snippet " + snipName, e);
            }
            snipName = name + ".dl." + cnt;
            dl = trans.getSnippet(snipName);
            cnt ++;
        } while(dl != null);
    }

}
