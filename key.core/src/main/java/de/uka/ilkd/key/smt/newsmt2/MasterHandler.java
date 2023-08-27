/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import de.uka.ilkd.key.smt.newsmt2.SMTHandler.Capability;

/**
 * Instances of this class are the controlling units of the translation. They control how the
 * translation is delegated to different {@link SMTHandler}s and collects the translations.
 *
 * It keeps track of the actual translation of an expression but collects also the declarations and
 * axioms that occur during the translation.
 *
 * It has measures to ensure that symbols are defined and axiomatized at most once. This allows us
 * to add these entries on the fly and on demand.
 *
 * @author Mattias Ulbrich
 * @author Jonas Schiffl
 */
public class MasterHandler {

    /** the services object associated with this particular translation */
    private final Services services;

    /** Exceptions that occur during translation */
    private final List<Throwable> exceptions = new ArrayList<>();

    /** The different handlers */
    private final List<SMTHandler> handlers;

    /** All declarations (declare-fun ...), (declare-const ...) */
    private final List<Writable> declarations = new ArrayList<>();

    /** All axioms (assert ...) */
    private final List<Writable> axioms = new ArrayList<>();

    /** A list of known symbols */
    private final Set<String> knownSymbols = new HashSet<>();

    /** A list of untranslatable values */
    private final Map<Term, SExpr> unknownValues = new HashMap<>();

    /** The collected set of sorts occurring in the problem */
    private final Set<Sort> sorts = new HashSet<>();

    /**
     * Global state, e.g., a counter for the number of distinct field variables Handlers can make
     * use of this to store translation-specific data.
     */
    private final Map<String, Object> translationState = new HashMap<>();

    /**
     * A map from a logic operator to the handler which can work on it. If a handler is in this map,
     * it has promised to deal with all terms with the operator as toplevel operator.
     */
    private final Map<Operator, SMTHandler> handlerMap = new IdentityHashMap<>();

    /**
     * Create a new handler with the default set of smt handlers.
     *
     * @param services non-null services
     * @param settings settings from the proof for the property settings.
     * @param handlerNames fully qualified class names of the handlers to use. If empty, all
     *        available handlers are used.
     * @param handlerOptions arbitrary String options for the handlers to process
     * @throws IOException if the handlers cannot be loaded
     */
    public MasterHandler(Services services, SMTSettings settings, @Nullable String[] handlerNames,
            String[] handlerOptions) throws IOException {
        this.services = services;
        getTranslationState().putAll(settings.getNewSettings().getMap());
        handlers = SMTHandlerServices.getInstance().getFreshHandlers(services, handlerNames,
            handlerOptions, this);
    }

    /**
     * Copy toplevel declarations and axioms from a collection of snippets directly and make all
     * named declarations (name.decl) and axioms (name.axioms)
     *
     * @param snippets
     */
    public void addDeclarationsAndAxioms(Properties snippets) {
        String decls = snippets.getProperty("decls");
        if (decls != null) {
            addDeclaration(new VerbatimSMT(decls));
        }

        String axioms = snippets.getProperty("axioms");
        if (axioms != null) {
            addAxiom(new VerbatimSMT(axioms));
        }

        for (Entry<Object, Object> en : snippets.entrySet()) {
            String key = (String) en.getKey();
            if (key.endsWith(".decls") || key.endsWith(".axioms")) {
                translationState.put(key, en.getValue());
            }
        }
    }

    /**
     * This interface is used for routines that can be used to flexibly introduce function symbols.
     *
     * An instance can be stored in the {@link #translationState} with a key suffixed with ".intro".
     * It is then invoked when a symbol is to be introduced.
     */
    @FunctionalInterface
    public interface SymbolIntroducer {
        void introduce(MasterHandler masterHandler, String name) throws SMTTranslationException;
    }

    /**
     * Translate a single term to an SMTLib S-Expression.
     *
     * This method may modify the state of the handler (by adding symbols e.g.).
     *
     * It tries to find a {@link SMTHandler} that can deal with the argument and delegates to that.
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
                switch (response) {
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
        } catch (Exception ex) {
            exceptions.add(ex);
            return handleAsUnknownValue(problem);
        }
    }

    /**
     * Translate a single term to an SMTLib S-Expression.
     *
     * The result is ensured to have the SExpr-Type given as argument. If the type coercion fails,
     * then the translation falls back to translating the argument as an unknown function.
     *
     * This method may modify the state of the handler (by adding symbols e.g.).
     *
     * It tries to find a {@link SMTHandler} that can deal with the argument and delegates to that.
     *
     * A default translation is triggered if no handler can be found.
     *
     * @param problem the non-null term to translate
     * @param type the type of the resulting s-expression
     * @return the S-Expression representing the translation
     */
    public SExpr translate(Term problem, Type type) {
        try {
            return SExprs.coerce(translate(problem), type);
        } catch (Exception ex) {
            // Fall back to an unknown value despite the exception.
            // The result will still be valid SMT code then.
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
     *
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
     *
     * This means that an expression of the form
     *
     * <pre>
     *     (functionName t1 ... tn)
     * </pre>
     *
     * is returned where t1, ..., tn are the smt-translations of the subterms of term.
     *
     * @param functionName the name of the function
     * @param term the term to be translated
     * @return an expression with the name functionName and subterms as children
     */
    SExpr handleAsFunctionCall(String functionName, Term term) {
        return handleAsFunctionCall(functionName, Type.UNIVERSE, term);
    }

    /**
     * Treats the given term as a function call.
     *
     * This means that an expression of the form
     *
     * <pre>
     *     (functionName t1 ... tn)
     * </pre>
     *
     * is returned where t1, ..., tn are the smt-translations of the sub-terms of term.
     *
     * @param functionName the name of the function
     * @param type the type of the resulting s-expression
     * @param term the term to be translated
     * @return an expression with the name functionName and the term's sub-terms as children
     */
    SExpr handleAsFunctionCall(String functionName, Type type, Term term) {
        List<SExpr> children = new ArrayList<>();
        for (int i = 0; i < term.arity(); i++) {
            children.add(translate(term.sub(i), Type.UNIVERSE));
        }
        return new SExpr(functionName, type, children);
    }

    /**
     * Decides whether a symbol is already known to the master handler.
     *
     * @param pr the SMT symbol name to test
     * @return true iff the name is already known
     */
    boolean isKnownSymbol(String pr) {
        return knownSymbols.contains(pr);
    }

    void addKnownSymbol(String symbol) {
        assert !knownSymbols.contains(symbol) : symbol + " already known";
        knownSymbols.add(symbol);
    }

    public List<Throwable> getExceptions() {
        return exceptions;
    }

    /**
     * Translate a list of terms into a list of SExprs.
     *
     * @param terms non-null list of terms.
     * @param type the non-null smt type to coerce to
     * @return a list of translations
     * @throws SMTTranslationException if the type conversion is impossible
     */
    public List<SExpr> translate(Iterable<Term> terms, Type type) throws SMTTranslationException {
        return SExprs.coerce(translate(terms), type);
    }

    /**
     * Translate a list of terms into a list of SExprs without coercion.
     *
     * @param terms non-null list of terms.
     * @return a list of translations
     */
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

    void introduceSymbol(String functionName) throws SMTTranslationException {
        if (isKnownSymbol(functionName)) {
            return;
        }

        if (translationState.containsKey(functionName + ".intro")) {
            SymbolIntroducer introducer =
                (SymbolIntroducer) translationState.get(functionName + ".intro");
            introducer.introduce(this, functionName);
        }

        // Handle it locally.
        // mark it known to avoid cyclic inclusion (if not already registered)
        if (!isKnownSymbol(functionName)) {
            addKnownSymbol(functionName);
        }

        if (translationState.containsKey(functionName + ".decls")) {
            String decls = (String) translationState.get(functionName + ".decls");
            VerbatimSMT decl = new VerbatimSMT(decls);
            addDeclaration(decl);
        }

        if (translationState.containsKey(functionName + ".axioms")) {
            String axioms = (String) translationState.get(functionName + ".axioms");
            VerbatimSMT ax = new VerbatimSMT(axioms);
            addAxiom(ax);
        }

        if (translationState.containsKey(functionName + ".deps")) {
            String entry = (String) translationState.get(functionName + ".deps");
            String[] deps = entry.trim().split(", *");
            for (String dep : deps) {
                introduceSymbol(dep);
            }
        }

    }

    Map<String, Object> getTranslationState() {
        return translationState;
    }
}
