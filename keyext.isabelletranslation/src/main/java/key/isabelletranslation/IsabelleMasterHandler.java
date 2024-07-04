package key.isabelletranslation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.*;

public class IsabelleMasterHandler {

    private final Services services;

    private final List<Throwable> exceptions = new ArrayList<>();

    private final List<IsabelleHandler> handlers;

    private final List<StringBuilder> preambles = new ArrayList<>();

    /**
     * A list of untranslatable values
     */
    private final Map<Operator, StringBuilder> unknownValues = new HashMap<>();

    private final Map<Sort, StringBuilder> predefinedSorts = new HashMap<>();

    private final Map<Sort, StringBuilder> extraSorts = new HashMap<>();

    private final Map<Operator, IsabelleHandler> handlerMap = new IdentityHashMap<>();
    private final List<StringBuilder> locales = new ArrayList<>();

    private final Collection<String> constDeclarations = new HashSet<>();

    private final Collection<StringBuilder> newFields = new HashSet<>();

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
        this.services = services;
        List<IsabelleHandler> handlers = IsabelleHandlerServices.getInstance().getFreshHandlers(services, handlerNames, handlerOptions, this);
        predefinedSorts.put(Sort.ANY, new StringBuilder("any"));
        predefinedSorts.put(Sort.FORMULA, new StringBuilder("bool"));
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
            exceptions.add(new SMTTranslationException("Couldn't translate: \"" + problem.op().name().toString() + "\""));
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
        if (unknownValues.containsKey(problem.op())) {
            return unknownValues.get(problem.op());
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

    protected boolean addField(Function field) {
        assert (field.sort() == services.getNamespaces().sorts().lookup("Field") && field.arity() == 0);
        return newFields.add(unknownValues.get(field));
    }

    protected Collection<StringBuilder> getNewFields() {
        return newFields;
    }

    private void addConstDeclaration(Term term) {
        StringBuilder decl = new StringBuilder();
        assert unknownValues.get(term.op()) != null;
        decl.append("fixes ");
        decl.append(unknownValues.get(term.op()));
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
        constDeclarations.add(decl.toString());
    }

    boolean isNewSymbol(Term term) {
        return !unknownValues.containsKey(term.op());
    }

    boolean isNewSort(Sort s) {
        return (!predefinedSorts.containsKey(s) && !extraSorts.containsKey(s));
    }

    void addGenericSort(Sort sort) {
        if (isNewSort(sort)) {
            extraSorts.put(sort, new StringBuilder(sort.name().toString().replace("[]", "arr").replace(".", "_")));
            if (sort instanceof ArraySort) {
                addGenericSort(((ArraySort) sort).elementSort());
            }
        }
    }

    void addPreamble(StringBuilder stringBuilder) {
        preambles.add(stringBuilder);
    }

    List<StringBuilder> getPreambles() {
        return preambles;
    }

    String translateSortName(Sort sort) {
        if (isNewSort(sort)) {
            addGenericSort(sort);
        }
        if (predefinedSorts.containsKey(sort)) {
            return predefinedSorts.get(sort).toString();
        }
        return extraSorts.get(sort).toString();
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

    void addPredefinedSort(Sort s, String name) {
        predefinedSorts.put(s, new StringBuilder(name));
    }

    Set<Sort> getExtraSorts() {
        return extraSorts.keySet();
    }

    void addKnownSymbol(Term term, StringBuilder s) {
        unknownValues.put(term.op(), s);
        addConstDeclaration(term);
    }

    StringBuilder getKnownSymbol(Term term) {
        return unknownValues.get(term.op());
    }

    Collection<String> getConstDeclarations() {
        return constDeclarations;
    }

    Set<Sort> getPredefinedSorts() {
        return predefinedSorts.keySet();
    }

    List<Throwable> getExceptions() {
        return exceptions;
    }
}
