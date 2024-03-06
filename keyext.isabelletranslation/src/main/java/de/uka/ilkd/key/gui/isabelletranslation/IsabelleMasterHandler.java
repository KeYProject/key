package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

import java.io.IOException;
import java.util.*;

public class IsabelleMasterHandler {

    private final List<Throwable> exceptions = new ArrayList<>();

    private final List<IsabelleHandler> handlers;

    private final List<StringBuilder> preambles = new ArrayList<>();

    /**
     * A list of untranslatable values
     */
    private final Map<Operator, StringBuilder> unknownValues = new HashMap<>();

    private final Set<Sort> predefinedSorts = new HashSet<>();

    private final Set<Sort> extraSorts = new HashSet<>();

    private final Map<Operator, IsabelleHandler> handlerMap = new IdentityHashMap<>();
    private final List<StringBuilder> locales = new ArrayList<>();

    private final List<StringBuilder> constDeclarations = new ArrayList<>();

    /**
     * Create a new handler with the default set of smt handlers.
     *
     * @param services       non-null services
     * @param handlerNames   fully qualified class names of the handlers to use. If empty, all
     *                       available handlers are used.
     * @param handlerOptions arbitrary String options for the handlers to process
     * @throws IOException if the handlers cannot be loaded
     */
    public IsabelleMasterHandler(Services services, String[] handlerNames,
                                 String[] handlerOptions) throws IOException {
        //TODO efficient loading of handlers. See MasterHandler in SMT
        List<IsabelleHandler> handlers = IsabelleHandlerServices.getInstance().getFreshHandlers(services, handlerNames, handlerOptions, this);
        predefinedSorts.add(Sort.ANY);
        predefinedSorts.add(Sort.FORMULA);
        this.handlers = handlers;
    }

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

            return handleAsUnknownValue(problem);
        } catch (Exception ex) {
            exceptions.add(ex);
            return handleAsUnknownValue(problem);
        }
    }

    public List<StringBuilder> translate(Iterable<Term> terms) {
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
        if (unknownValues.containsKey(problem)) {
            return unknownValues.get(problem);
        }
        int number = unknownValues.size();
        StringBuilder translation;
        StringBuilder abbr = new StringBuilder("unknown_" + problem.op().name().toString());
        var freeVars = problem.freeVars();
        if (freeVars.isEmpty()) {
            // simple case: unknown value does not depend on anything else
        } else {
            // unknown value depends on quantified variables
            //TODO implement this
        }
        unknownValues.put(problem.op(), abbr);
        return abbr;
    }

    private void addConstDeclaration(Term term) {
        StringBuilder decl = new StringBuilder();
        assert unknownValues.get(term.op()) != null;
        decl.append("fixes ");
        decl.append(unknownValues.get(term.op()));
        decl.append("::\"");
        for (Term sub : term.subs()) {
            if (!isKnownSort(sub.sort())) {
                addSort(sub.sort());
            }
            decl.append(sub.sort().name().toString()).append("=>");
        }
        decl.append((term.sort() == Sort.FORMULA ? "bool" : term.sort().name().toString()));
        decl.append("\"");
        constDeclarations.add(decl);
    }

    boolean isKnownSymbol(Term term) {
        return unknownValues.containsKey(term.op());
    }

    boolean isKnownSort(Sort s) {
        return (predefinedSorts.contains(s) || extraSorts.contains(s));
    }

    void addSort(Sort sort) {
        if (!isKnownSort(sort)) {
            extraSorts.add(sort);
        }
    }

    void addPreamble(StringBuilder stringBuilder) {
        preambles.add(stringBuilder);
    }

    List<StringBuilder> getPreambles() {
        return preambles;
    }


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

    void addLocale(StringBuilder stringBuilder) {
        locales.add(stringBuilder);
    }

    List<StringBuilder> getLocales() {
        return locales;
    }

    void addPredefinedSort(Sort s) {
        predefinedSorts.add(s);
    }

    Set<Sort> getExtraSorts() {
        return extraSorts;
    }

    void addKnownSymbol(Term term, StringBuilder s) {
        unknownValues.put(term.op(), s);
        addConstDeclaration(term);
    }

    StringBuilder getKnownSymbol(Term term) {
        return unknownValues.get(term.op());
    }

    List<StringBuilder> getConstDeclarations() {
        return constDeclarations;
    }
}
