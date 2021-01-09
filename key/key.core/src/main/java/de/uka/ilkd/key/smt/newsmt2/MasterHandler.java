package de.uka.ilkd.key.smt.newsmt2;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.ServiceLoader;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import de.uka.ilkd.key.smt.newsmt2.SMTHandler.Capability;

public class MasterHandler {

    /** the services object associated with this particular translation */
    private final Services services;

    /** Exceptions that occur during translation */
    private final List<Throwable> exceptions = new ArrayList<>();

    /** The different handlers */
    private final List<SMTHandler> handlers = new ArrayList<>();

    /** All declarations (declare-fun ...), (declare-const ...) */
    private final List<Writable> declarations = new ArrayList<>();

    /** All axioms (assert ...)*/
    private final List<Writable> axioms = new ArrayList<>();

    /** All SMT options */
    private final List<Writable> options = new ArrayList<>();

    /** A list of known symbols */
    private final Set<String> knownSymbols = new HashSet<>();

    /** A list of untranslatable values*/
    private final Map<Term, SExpr> unknownValues = new HashMap<>();

    /** The collected content of the properties files that
     * belong to the different handlers
     */
    private final Properties snippets = new Properties();

    /** The collected set of sorts occurring in the problem */
    private final Set<Sort> sorts = new HashSet<>();

    /** Global state, e.g., a counter for the number of distinct field variables
     * Handlers can make use of this to store translation-specific data.
     */
    private final Map<String, Object> translationState = new HashMap<>();

    /**
     * A map from a logic operator to the handler which can work on it.
     * If a handler is in this map, it has promised to deal with all terms
     * with the operator as toplevel operator.
     */
    private final Map<Operator, SMTHandler> handlerMap = new IdentityHashMap<>();

    public MasterHandler(Services services) throws IOException {

        this.services = services;

        snippets.loadFromXML(getClass().getResourceAsStream("preamble.xml"));

        for (SMTHandler smtHandler : ServiceLoader.load(SMTHandler.class)) {
            Properties handlerSnippets = loadSnippets(smtHandler.getClass());
            smtHandler.init(this, services, handlerSnippets);
            if (handlerSnippets != null) {
                snippets.putAll(handlerSnippets);
            }
            handlers.add(smtHandler);
        }


        // If there are options in the preamble pass them through verbatim.
        if (snippets.containsKey("opts")) {
            VerbatimSMT opts = new VerbatimSMT(snippets.getProperty("opts"));
            addOption(opts);
        }

        // sort the entries in the snippets to make this deterministic
        SortedSet<Object> keys = new TreeSet<>(snippets.keySet());
        for (Object k : keys) {
            String key = k.toString();
            if(key.endsWith(".auto")) {
                // strip the ".auto" and add the snippet
                addFromSnippets(key.substring(0, key.length() - 5));
            }
        }

    }

    /**
     * Translate a single term to an SMTLib S-Expression.
     *
     * This method may modify the state of the handler (by adding symbols e.g.).
     *
     * It tries to find a {@link SMTHandler} that can deal with the argument
     * and delegates to that.
     *
     * A default translation is triggered if no handler can be found.
     *
     * @param problem the non-null term to translate
     * @return the S-Expression representing the translation
     */
    public SExpr translate(Term problem) {

        try {
            SMTHandler cached = handlerMap.get(problem.op());
            if (cached != null) {
                // There is a handler that promised to handle this operator ...
                return cached.handle(this, problem);
            }

            for (SMTHandler smtHandler : handlers) {
                Capability response = smtHandler.canHandle(problem);
                switch(response) {
                    case YES_THIS_INSTANCE:
                        // handle this but do not cache.
                        return smtHandler.handle(this, problem);
                    case YES_THIS_OPERATOR:
                        // handle it and cache it for future instances of the op.
                        handlerMap.put(problem.op(), smtHandler);
                        return smtHandler.handle(this, problem);
                }
            }

            return handleAsUnknownValue(problem);
        } catch(Exception ex) {
            exceptions.add(ex);
            return handleAsUnknownValue(problem);
        }
    }

    /**
     * Translate a single term to an SMTLib S-Expression.
     *
     * The result is ensured to have the SExpr-Type given as argument.
     * If the type coercion fails, then the translation falls back to
     * translating the argument as an unknown function.
     *
     * This method may modify the state of the handler (by adding symbols e.g.).
     *
     * It tries to find a {@link SMTHandler} that can deal with the argument
     * and delegates to that.
     *
     * A default translation is triggered if no handler can be found.
     *
     * @param problem the non-null term to translate
     * @return the S-Expression representing the translation
     */
    public SExpr translate(Term problem, Type type)  {
        try {
            return SExprs.coerce(translate(problem), type);
        }  catch(Exception ex) {
            exceptions.add(ex);
            try {
                return SExprs.coerce(handleAsUnknownValue(problem), type);
            } catch (SMTTranslationException e) {
                // This can actually never happen since a universe element is translated
                throw new Error(e);
            }
        }
    }

    /**
     * If no handler can handle a term, it is taken care of here.
     * @param problem the problematic term
     * @return a generic translation as unknown value
     */
    private SExpr handleAsUnknownValue(Term problem) {
        if (unknownValues.containsKey(problem)) {
            return unknownValues.get(problem);
        }
        int number = unknownValues.size();
        SExpr abbr = new SExpr("unknown_" + number, Type.UNIVERSE);
        SExpr e = new SExpr("declare-const", Type.UNIVERSE, abbr.toString(), "U");
        addAxiom(e);
        unknownValues.put(problem, abbr);
        return abbr;
    }

    /**
     * Treats the given term as a function call.
     * @param functionName the name of the function
     * @param term the term to be translated
     * @return an expression with the name functionName and subterms as children
     */
    SExpr handleAsFunctionCall(String functionName, Term term) {
        return handleAsFunctionCall(functionName, Type.UNIVERSE, term);
    }

    /**
     * Treats the given term as a function call.
     * @param functionName the name of the function
     * @param term the term to be translated
     * @return an expression with the name functionName and subterms as children
     */
    SExpr handleAsFunctionCall(String functionName, Type type, Term term) {
        addFromSnippets(functionName);
        List<SExpr> children = new ArrayList<>();
        for (int i = 0; i < term.arity(); i++) {
            children.add(translate(term.sub(i), Type.UNIVERSE));
        }
        return new SExpr(functionName, type, children);
    }

    /**
     * Decides whether a symbol is already known to the master handler.
     * @param pr the string to test
     * @return true iff the name is already known
     */
    boolean isKnownSymbol(String pr) {
        return knownSymbols.contains(pr);
    }

    void addKnownSymbol(String symbol) {
        knownSymbols.add(symbol);
    }

    public List<Throwable> getExceptions() {
        return exceptions;
    }

    public List<SExpr> translate(Iterable<Term> terms, Type type) throws SMTTranslationException {
        return SExprs.coerce(translate(terms), type);
    }

    public List<SExpr> translate(Iterable<Term> terms) {
        List<SExpr> result = new LinkedList<>();
        for (Term term : terms) {
            result.add(translate(term));
        }
        return result;
    }

    public List<Writable> getDeclarations() {
        return declarations;
    }

    void addDeclaration(Writable decl) {
        declarations.add(decl);
    }

    void addAxiom(Writable decl) {
        axioms.add(decl);
    }

    public List<Writable> getAxioms() {
        return axioms;
    }

    public void addSort(Sort s) {
        sorts.add(s);
    }

    public Set<Sort> getSorts() {
        return sorts;
    }

    public Map<Term, SExpr> getUnknownValues() {
        return unknownValues;
    }

    public List<Writable> getOptions() {
        return options;
    }

    public void addOption(Writable w) {
        options.add(w);
    }

    void addFromSnippets(String functionName) {
        if (isKnownSymbol(functionName)) {
            return;
        }

        // mark it known to avoid cyclic inclusion
        addKnownSymbol(functionName);

        if (snippets.containsKey(functionName + ".decls")) {
            VerbatimSMT decl = new VerbatimSMT(snippets.getProperty(functionName + ".decls"));
            addDeclaration(decl);
        }

        if (snippets.containsKey(functionName + ".axioms")) {
            VerbatimSMT ax = new VerbatimSMT(snippets.getProperty(functionName + ".axioms"));
            addAxiom(ax);
        }

        String[] deps = snippets.getProperty(functionName + ".deps", "").trim().split(", *");
        for (String dep : deps) {
            addFromSnippets(dep);
        }
    }

    Map<String, Object> getTranslationState() {
        return translationState;
    }

    /**
     * @deprecated Use SExprs.coerce
     */
    @Deprecated
    public SExpr coerce(SExpr sExpr, Type type) throws SMTTranslationException {
        return SExprs.coerce(sExpr, type);
    }

    private static Properties loadSnippets(Class<?> aClass) throws IOException {
        String resourceName = aClass.getSimpleName() + ".preamble.xml";
        URL resource = aClass.getResource(resourceName);
        if (resource != null) {
            Properties snippets = new Properties();
            try (InputStream is = resource.openStream()) {
                snippets.loadFromXML(is);
            }
            return snippets;
        }
        return null;
    }

    public String getSnippet(String s) {
        return snippets.getProperty(s);
    }

    public String getSnippet(String s, String orElse) {
        return snippets.getProperty(s, orElse);
    }

    public Writable getSnippet(String s, Writable orElse) {
        String result = snippets.getProperty(s);
        if (result == null) {
            return orElse;
        } else {
            return new VerbatimSMT(result);
        }
    }

    public boolean hasSnippet(String s) {
        return snippets.containsKey(s);
    }
}
