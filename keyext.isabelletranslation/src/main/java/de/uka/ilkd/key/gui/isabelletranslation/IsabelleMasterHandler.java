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

    private final List<StringBuilder> constDeclarations = new ArrayList<>();


    private final Set<String> knownSymbols = new HashSet<>();

    /**
     * A list of untranslatable values
     */
    private final Map<Term, StringBuilder> unknownValues = new HashMap<>();

    private final Set<Sort> sorts = new HashSet<>();

    private final Map<Operator, IsabelleHandler> handlerMap = new IdentityHashMap<>();

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
        StringBuilder abbr = new StringBuilder("unknown_" + number);
        var freeVars = problem.freeVars();
        if (freeVars.isEmpty()) {
            // simple case: unknown value does not depend on anything else
            StringBuilder e = new StringBuilder("consts" + System.lineSeparator() + abbr + "::Any");
            addConstDeclaration(e);
            translation = abbr;
        } else {
            // unknown value depends on quantified variables
            //TODO implement this
        }
        unknownValues.put(problem, abbr);
        return null;
    }

    void addConstDeclaration(StringBuilder decl) {
        constDeclarations.add(decl);
    }

    boolean isKnownSort(Sort s) {
        return sorts.contains(s);
    }

    StringBuilder createSortDecl(Sort sort) {
        //TODO IMPLEMENT
        return new StringBuilder();
    }

    boolean addSort(Sort sort) {
        if (!isKnownSort(sort)) {
            sorts.add(sort);
        }
        return false;
    }

    boolean isKnownSymbol(String name) {
        return knownSymbols.contains(name);
    }

    public void addPreamble(StringBuilder stringBuilder) {
        preambles.add(stringBuilder);
    }

    public List<StringBuilder> getPreambles() {
        return preambles;
    }

    public void addKnownSymbol(String name) {
        knownSymbols.add(name);
    }

    public void addPreambles(Properties handlerSnippets) {
        for (Map.Entry<Object, Object> entry : handlerSnippets.entrySet()) {
            String key = (String) entry.getKey();
            if (key.endsWith(".preamble")) {
                addPreamble(new StringBuilder((String) entry.getValue()));
            }
        }
    }
}
