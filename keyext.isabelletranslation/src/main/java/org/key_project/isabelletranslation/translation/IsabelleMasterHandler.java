/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

/**
 * This class is responsible for translating the sequent of a given goal.
 * It collects all declarations and definitions which need to be added to the translation.
 * <p>
 * The sequent is repeatedly given to the respective {@link IsabelleHandler}, which can translate
 * its top most operator.
 *
 * @author Nils Buchholz
 */
public class IsabelleMasterHandler {

    /**
     * The services object used to obtain the namespace for standard sorts in KeY
     */
    private final Services services;

    /**
     * The exceptions thrown by handlers during translation.
     */
    private final List<Throwable> exceptions = new ArrayList<>();

    /**
     * The list of handlers to be used for translation.
     */
    private final List<IsabelleHandler> handlers;

    /**
     * The preambles added for each of the handlers.
     * Currently only two such preambles exist, separating this preamble into multiple preambles is
     * a complex undertaking due to various dependencies within it.
     */
    private final List<StringBuilder> preambles = new ArrayList<>();

    /**
     * A list of the names of locales that need to be added to the translation locale.
     * These can be added by the handler
     */
    private final List<StringBuilder> locales = new ArrayList<>();

    /**
     * A map of operators that were not predefined and their respective translations
     */
    private final Map<Operator, StringBuilder> notPredefinedFunctions = new HashMap<>();

    /**
     * A map of predefined sorts and their translations
     */
    private final Map<Sort, StringBuilder> predefinedSorts = new HashMap<>();

    /**
     * A map of sorts that were not predefined and for which a definition needs to be generated in
     * the translation theory and their translations.
     */
    private final Map<Sort, StringBuilder> extraSorts = new HashMap<>();

    /**
     * Stores handlers who are able to handle a given operator to avoid searching through the list
     * of handlers
     */
    private final Map<Operator, IsabelleHandler> handlerMap = new IdentityHashMap<>();

    /**
     * The declarations that are added to the locale to introduce variables and functions only found
     * on the sequent
     */
    private final Collection<String> variableDeclarations = new HashSet<>();

    /**
     * A collection of all fields. These require separate storage to add the lemma stating that they
     * are separate values.
     */
    private final Collection<StringBuilder> newFields = new HashSet<>();

    /**
     * Create a new handler with the default set of Isabelle handlers.
     *
     * @param services non-null services
     * @param handlerNames fully qualified class names of the handlers to use. If empty, all
     *        available handlers are used.
     * @param handlerOptions arbitrary String options for the handlers to process
     * @throws IOException if the handlers cannot be loaded
     */
    public IsabelleMasterHandler(Services services, String[] handlerNames,
            String[] handlerOptions) throws IOException {
        this.services = services;
        List<IsabelleHandler> handlers = IsabelleHandlerServices.getInstance()
                .getFreshHandlers(services, handlerNames, handlerOptions, this);
        predefinedSorts.put(JavaDLTheory.ANY, new StringBuilder("any"));
        predefinedSorts.put(JavaDLTheory.FORMULA, new StringBuilder("bool"));
        this.handlers = handlers;
    }

    /**
     * Translates the given term using the handlers.
     *
     * @param problem the problem to be translated
     * @return a string builder containing the translation of the sequent (does not contain the full
     *         Isabelle theory necessary for proof search. for that see
     *         {@link IsabelleTranslator#translateProblem(Goal)})
     */
    public StringBuilder translate(Term problem) {
        try {
            IsabelleHandler cached = handlerMap.get(problem.op());
            if (cached != null) {
                // There is a handler that promised to handle this operator ...
                return cached.handle(this, problem);
            }

            for (IsabelleHandler isabelleHandler : handlers) {
                IsabelleHandler.Capability response = isabelleHandler.canHandle(problem);
                switch (response) {
                    case YES_THIS_INSTANCE -> {
                        // handle this but do not cache.
                        return isabelleHandler.handle(this, problem);
                    }
                    case YES_THIS_OPERATOR -> {
                        // handle it and cache it for future instances of the op.
                        handlerMap.put(problem.op(), isabelleHandler);
                        return isabelleHandler.handle(this, problem);
                    }
                }
            }
            exceptions.add(new IllegalFormulaException(
                "Couldn't translate: \"" + problem.op().name() + "\""));
            return handleAsUnknownValue(problem);
        } catch (Exception ex) {
            exceptions.add(ex);
            return handleAsUnknownValue(problem);
        }
    }

    /**
     * Translates multiple terms in the same manner as {@link IsabelleMasterHandler#translate(Term)}
     *
     * @param terms terms to be translated
     * @return a List of StringBuilders containing translations in the same order as the given terms
     */
    public List<StringBuilder> translate(ImmutableArray<? extends Term> terms) {
        List<StringBuilder> result = new LinkedList<>();
        for (Term term : terms) {
            result.add(translate(term));
        }
        return result;
    }

    /**
     * If no handler can handle a term, it is taken care of here.
     *
     * @param problem the problematic term
     * @return a generic translation as unknown value
     */
    private StringBuilder handleAsUnknownValue(Term problem) {
        if (notPredefinedFunctions.containsKey(problem.op())) {
            return notPredefinedFunctions.get(problem.op());
        }
        StringBuilder abbr = new StringBuilder("unknown_" + problem.op().name());
        notPredefinedFunctions.put(problem.op(), abbr);
        return abbr;
    }

    /**
     * Adds a field value to the newFields collection
     *
     * @param field a field value
     */
    protected void addField(@NonNull Function field) {
        assert (field.sort() == services.getNamespaces().sorts().lookup("Field")
                && field.arity() == 0);
        newFields.add(notPredefinedFunctions.get(field));
    }

    /**
     * Returns the fields not predefined, but found on the sequent.
     *
     * @return the list of fields found during translation
     */
    protected Collection<StringBuilder> getNewFields() {
        return newFields;
    }

    /**
     * Adds the necessary line to declare the top-most operator of the given term in the translation
     * locale.
     *
     * @param term the term whose top-most operator is supposed to be introduced
     */
    private void addVariableDeclaration(@NonNull Term term) {
        StringBuilder decl = new StringBuilder();
        assert notPredefinedFunctions.get(term.op()) != null;
        decl.append("fixes ");
        decl.append(notPredefinedFunctions.get(term.op()));
        decl.append("::\"");

        if (term.op() instanceof SortedOperator) {
            SortedOperator op = (SortedOperator) term.op();
            for (Sort argSort : op.argSorts()) {
                if (isNewSort(argSort)) {
                    addGenericSort(argSort);
                }
                decl.append(translateSortName(argSort)).append("=>");
            }
            decl.append((translateSortName(op.sort())));
            decl.append("\"");
        } else {
            for (Term sub : term.subs()) {
                if (isNewSort(sub.sort())) {
                    addGenericSort(sub.sort());
                }
                decl.append(translateSortName(sub.sort())).append("=>");
            }
            decl.append((translateSortName(term.sort())));
            decl.append("\"");
        }
        variableDeclarations.add(decl.toString());
    }

    /**
     * Checks whether the given top-most operator of the given term is not predefined
     * Used for handlers to check if they need to add a declaration to the translation locale
     *
     * @param term the term whose top-most operator is
     * @return true - the top-most operator is not predefined, false otherwise
     */
    boolean isNewSymbol(Term term) {
        return !notPredefinedFunctions.containsKey(term.op());
    }

    /**
     * Checks if a given sort has not been defined already.
     *
     * @param s the sort to check for
     * @return true - the sort was not defined yet, false otherwise
     */
    boolean isNewSort(Sort s) {
        return (!predefinedSorts.containsKey(s) && !extraSorts.containsKey(s));
    }

    /**
     * Adds a generic sort to the translation. A generic sort in this context means a sort that is
     * not part of the core vocabulary of JFOL as introduced in the KeY book. Examples include java
     * class sorts
     *
     * @param sort the sort to be introduced
     */
    void addGenericSort(@NonNull Sort sort) {
        if (isNewSort(sort)) {
            extraSorts.put(sort,
                new StringBuilder(sort.name().toString().replace("[]", "arr").replace(".", "_")));
            if (sort instanceof ArraySort) {
                addGenericSort(((ArraySort) sort).elementSort());
            }
        }
    }

    /**
     * Adds a preamble to the translation.
     *
     * @param stringBuilder the preamble in form of a stringbuilder
     */
    void addPreamble(StringBuilder stringBuilder) {
        preambles.add(stringBuilder);
    }

    /**
     * Returns the list of preambles for the translation
     *
     * @return the list of preambles
     */
    List<StringBuilder> getPreambles() {
        return preambles;
    }

    /**
     * Returns the translation of the given sort.
     *
     * @param sort sort whose translation is returned
     * @return String value containing the translation of the given sort
     */
    String translateSortName(@NonNull Sort sort) {
        if (isNewSort(sort)) {
            addGenericSort(sort);
        }
        if (predefinedSorts.containsKey(sort)) {
            return predefinedSorts.get(sort).toString();
        }
        return extraSorts.get(sort).toString();
    }


    /**
     * Adds the preambles and locales associated with the handlers
     *
     * @param handlerSnippets the snippets object containing the preambles/locales and their
     *        contents
     */
    void addPreamblesLocales(Properties handlerSnippets) {
        for (Map.Entry<Object, Object> entry : handlerSnippets.entrySet()) {
            String key = (String) entry.getKey();
            if (key.endsWith(".preamble")) {
                addPreamble(new StringBuilder((String) entry.getValue()));
            }
            if (key.endsWith(".locale")) {
                addLocale(new StringBuilder((String) entry.getValue()));
            }
        }
    }

    /**
     * Adds a locale name to the translation. This will be included in the translation locale
     *
     * @param stringBuilder name of the locale
     */
    void addLocale(@NonNull StringBuilder stringBuilder) {
        locales.add(stringBuilder);
    }

    /**
     * Returns the list of locales to be added to the translation locale
     *
     * @return list of locales
     */
    List<StringBuilder> getLocales() {
        return locales;
    }

    /**
     * Adds a sort to the predefined sorts list. Used by handlers that include their own preamble.
     *
     * @param s the sort that was predefined
     * @param name the name used for the sort in translation
     */
    void addPredefinedSort(@NonNull Sort s, String name) {
        predefinedSorts.put(s, new StringBuilder(name));
    }

    /**
     * Returns the sorts that require a generated declaration in the translation theory.
     *
     * @return Collection of the sorts that need to be declared in theory
     */
    Set<Sort> getExtraSorts() {
        return extraSorts.keySet();
    }

    /**
     * Adds the top-most operator of the term to the map containing operators and their
     * translations.
     * Also adds the necessary declaration line to the list of declarations
     *
     * @param term the term whose top-most operator is being added
     * @param s the translation of the top-most operator
     */
    void addSymbolAndDeclaration(Term term, StringBuilder s) {
        notPredefinedFunctions.put(term.op(), s);
        addVariableDeclaration(term);
    }

    /**
     * Returns the translation of a symbol introduced during translation (!not predefined)
     *
     * @param term the term whose top-most operator will be translated
     * @return translation of the top-most operator
     */
    StringBuilder getKnownSymbol(Term term) {
        return notPredefinedFunctions.get(term.op());
    }

    /**
     * Returns the declarations that need to be added to the translation locale
     *
     * @return collection of the declaration lines that need to be added to the translation locale
     */
    Collection<String> getVariableDeclarations() {
        return variableDeclarations;
    }

    /**
     * Returns the set of predefined sorts
     *
     * @return set of predefined sorts
     */
    Set<Sort> getPredefinedSorts() {
        return predefinedSorts.keySet();
    }

    /**
     * Returns the list of exceptions encountered during translation
     *
     * @return list of exceptions
     */
    List<Throwable> getExceptions() {
        return exceptions;
    }
}
