package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
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
            // symbol is constant (i.e. 0-ary) function or ProgramVariable
            return translateUninterpreted(symbol);
        } else if (symbol.startsWith(LOGICAL_VARIABLE_PREFIX)) {
            // Sort.Any serves as fallback here
            QuantifiableVariable qv = translateLogicVariable(symbol, Sort.ANY);
            return services.getTermBuilder().var(qv);
        } else if (symbol.startsWith(DEFINED_SYMBOL_PREFIX)) {
            return translateDefinedSymbol(symbol);
        }/* else if (symbol.startsWith(UNKNOWN_PREFIX)) {
            // TODO: what to do here?
        }*/
        return null;
    }

    public Term translateUninterpreted(String symbol) {
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

    public QuantifiableVariable translateLogicVariable(String symbol, Sort sort) {
        String origVarName = symbol.substring(LOGICAL_VARIABLE_PREFIX.length());
        QuantifiableVariable qv = services.getNamespaces().variables().lookup(origVarName);
        if (qv != null) {
            return qv;
        }
        // TODO: creates wrong symbols! return null here?
        return new LogicVariable(new Name(origVarName), sort);
    }

    public Term translateDefinedSymbol(String symbol) {
        String origName = symbol.substring(DEFINED_SYMBOL_PREFIX.length());
        // symbol could be a function (e.g. null), TODO: what else?
        Function f = services.getNamespaces().functions().lookup(origName);
        if (f != null) {
            // TODO: this only works for nullary functions!
            return services.getTermBuilder().func(f);
        }
        throw new IllegalStateException("Defined symbol not found: " + symbol);
    }

    public Sort translateSort(String symbol) {
        String origSortName = symbol.substring(SORT_PREFIX.length());
        Sort keySort = services.getNamespaces().sorts().lookup(origSortName);

        if (keySort == null) {
            throw new IllegalStateException("No sort " + origSortName + " is known to KeY!");
        }
        return keySort;
    }
}
