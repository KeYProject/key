package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.ServiceLoader;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class MasterHandler {

    private List<Throwable> exceptions = new ArrayList<>();

    private List<SMTHandler> handlers = new ArrayList<>();

    private List<SExpr> declarations = new ArrayList<>();

    private List<SExpr> axioms = new ArrayList<>();

    private Set<String> knownSymbols  = new HashSet<>();

    private HashSet<Sort> sorts = new HashSet<>();

    public MasterHandler(Services services) {

        for (SMTHandler smtHandler : ServiceLoader.load(SMTHandler.class)) {
            smtHandler.init(services);
            handlers.add(smtHandler);
        }
    }

    public SExpr translate(Term problem) {
        try {
            for (SMTHandler smtHandler : handlers) {
                if(smtHandler.canHandle(problem)) {
                    return smtHandler.handle(this, problem);
                }
            }
            return handleAsUnknownValue(problem);
        } catch(Exception ex) {
            exceptions.add(ex);
            return new SExpr("ERROR", Type.UNIVERSE);
        }
    }

    public SExpr translate(Term problem, Type type)  {
        try {
            return coerce(translate(problem), type);
        }  catch(Exception ex) {
            exceptions.add(ex);
            return new SExpr("ERROR", Type.UNIVERSE);
        }
    }

    private SExpr handleAsUnknownValue(Term problem) {
        String pr = "KeY_"+problem.toString();
        if(!isKnownSymbol(pr)) {
            addKnownSymbol(pr);
            addDeclaration(new SExpr("declare-const", pr, "U"));
        }
        return new SExpr(pr, Type.UNIVERSE);
    }

    public boolean isKnownSymbol(String pr) {
        return knownSymbols.contains(pr);
    }

    public void addKnownSymbol(String symbol) {
        knownSymbols.add(symbol);
    }

    public List<Throwable> getExceptions() {
        return exceptions;
    }

    public List<SExpr> translate(Iterable<Term> terms, Type type) throws SMTTranslationException {
        return coerce(translate(terms), type);
    }

    public List<SExpr> coerce(List<SExpr> exprs, Type type) throws SMTTranslationException {
        ListIterator<SExpr> it = exprs.listIterator();
        while(it.hasNext()) {
            it.set(coerce(it.next(), type));
        }
        return exprs;
    }

    public SExpr coerce(SExpr exp, Type type) throws SMTTranslationException {
        switch(type) {
        case BOOL:
            switch(exp.getType()) {
            case BOOL:
                return exp;
            case UNIVERSE:
                return new SExpr("u2b", Type.BOOL, exp);
            default:
                throw new SMTTranslationException("Cannot convert to bool: " + exp);
            }
        case INT:
            switch(exp.getType()) {
            case INT:
                return exp;
            case UNIVERSE:
                return new SExpr("u2i", Type.INT, exp);
            default:
                throw new SMTTranslationException("Cannot convert to int: " + exp);
            }
        case HEAP:
            switch(exp.getType()) {
            case HEAP:
                return exp;
            case UNIVERSE:
                return new SExpr("u2h", Type.INT, exp);
            default:
                throw new SMTTranslationException("Cannot convert to heap: " + exp);
            }
        case UNIVERSE:
            switch(exp.getType()) {
            case UNIVERSE:
                return exp;
            case INT:
                return new SExpr("i2u", Type.UNIVERSE, exp);
            case BOOL:
                return new SExpr("b2u", Type.UNIVERSE, exp);
            case HEAP:
                return new SExpr("h2u", Type.UNIVERSE, exp);
            default:
                throw new SMTTranslationException("Cannot convert to universe: " + exp);
            }
        default:
            throw new SMTTranslationException("Cannot convert into " + type);
        }
    }

    public List<SExpr> translate(Iterable<Term> terms) {
        List<SExpr> result = new LinkedList<>();
        for (Term term : terms) {
            result.add(translate(term));
        }
        return result;
    }

    public List<SExpr> getDeclarations() {
        return declarations;
    }

    public void addDeclaration(SExpr decl) {
        declarations.add(decl);
    }

    public void addAxiom(SExpr decl) {
        axioms.add(decl);
    }

    public List<SExpr> getAxioms() {
        return axioms;
    }

    public void addSort(Sort s) {
        sorts.add(s);
    }

    public HashSet<Sort> getSorts() {
        return sorts;
    }
}
