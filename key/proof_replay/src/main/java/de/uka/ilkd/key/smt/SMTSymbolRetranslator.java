package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Counterpart for SMTHandler (for symbols only).
 * @author Wolfram Pfeifer
 */
public class SMTSymbolRetranslator {
    // TODO: the prefixes are defined in various SMTHandlers
    public static final String UNINTERPRETED_PREFIX = "u_";
    public static final String LOGICAL_VARIABLE_PREFIX = "var_";
    public static final String DEFINED_SYMBOL_PREFIX = "k_";
    public static final String UNKNOWN_PREFIX = "unknown_";
    public static final String SORT_PREFIX = "sort_";

    private final Services services;

    public SMTSymbolRetranslator(Services services) {
        this.services = services;
    }

    public Term tryToTranslate(String symbol) {
        if (symbol.startsWith(UNINTERPRETED_PREFIX)) {
            return translateUninterpreted(symbol);
        } else if (symbol.startsWith(LOGICAL_VARIABLE_PREFIX)) {
            return translateLogicVariable(symbol);
        } else if (symbol.startsWith(DEFINED_SYMBOL_PREFIX)) {
            return translateDefinedConstSymbol(symbol);
        }/* else if (symbol.startsWith(UNKNOWN_PREFIX)) {
            // TODO: what to do here?
        }*/
        return null;
    }

    private Term translateUninterpreted(String symbol) {
        String origSym = symbol.substring(UNINTERPRETED_PREFIX.length());
        Function f = services.getNamespaces().functions().lookup(origSym);
        // symbol could be constant (i.e. 0-ary) function or ProgramVariable
        if (f != null) {
            return services.getTermBuilder().func(f);
        }
        IProgramVariable pv = services.getNamespaces().programVariables().lookup(origSym);
        if (pv instanceof ProgramVariable) {
            return services.getTermBuilder().var((ProgramVariable)pv);
        }
        throw new IllegalStateException("Uninterpreted symbol not found: " + symbol);
    }

    private Term translateLogicVariable(String symbol) {
        String origVarName = symbol.substring(LOGICAL_VARIABLE_PREFIX.length());
        QuantifiableVariable qv = services.getNamespaces().variables().lookup(origVarName);
        // note: can be null (will happen e.g. for skolem symbols)
        if (qv != null) {
            return services.getTermBuilder().var(qv);
        }
        return null;
    }

    // actually, defined symbol means function: here we handle only nullary functions!
    private Term translateDefinedConstSymbol(String symbol) {
        String origName = symbol.substring(DEFINED_SYMBOL_PREFIX.length());
        Function f = services.getNamespaces().functions().lookup(origName);
        if (f != null) {
            // this only works for nullary functions!
            return services.getTermBuilder().func(f);
        }
        throw new IllegalStateException("Defined symbol not found: " + symbol);
    }

    // for n-ary functions
    public Function translateDefinedSymbol(String symbol) {
        String origName = symbol.substring(DEFINED_SYMBOL_PREFIX.length());
        Function f = services.getNamespaces().functions().lookup(origName);
        if (f != null) {
            return f;
        }
        throw new IllegalStateException("Defined symbol not found: " + symbol);
    }

    // creates a new variable of given sort if none is found
    public QuantifiableVariable translateOrCreateLogicVariable(String symbol, Sort sort) {
        String origVarName = symbol;
        // cut prefix if present
        if (symbol.startsWith(LOGICAL_VARIABLE_PREFIX)) {
            origVarName = symbol.substring(LOGICAL_VARIABLE_PREFIX.length());
        }
        QuantifiableVariable qv = services.getNamespaces().variables().lookup(origVarName);
        // note: can be null (will happen e.g. for skolem symbols)
        if (qv != null) {
            return qv;
        }
        return new LogicVariable(new Name(origVarName), sort);
    }

    public Sort translateSort(String symbol) {
        // special sort, TODO: other special sorts?
        if (symbol.equals("Bool")) {
            return services.getTypeConverter().getBooleanType().getSort();
        } else if (symbol.equals("U")) {
            // special sort not existing in KeY; translate to any
            return Sort.ANY;
        }

        // cut prefix if present
        String origSortName = symbol;
        if (symbol.startsWith(SORT_PREFIX)) {
            origSortName = symbol.substring(SORT_PREFIX.length());
        }
        Sort keySort = services.getNamespaces().sorts().lookup(origSortName);
        if (keySort != null) {
            return keySort;
        }
        throw new IllegalStateException("No sort " + origSortName + " is known to KeY!");
    }
}
