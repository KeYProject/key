package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.util.Map;

public class FieldConstantHandler implements SMTHandler {

    public static final String CONSTANT_COUNTER_PROPERTY = "fieldConstant.counter";
    private Services services;

    @Override
    public void init(Services services) {
        this.services = services;
    }

    @Override
    public boolean canHandle(Term term) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        Operator op = term.op();
        return term.sort() == heapLDT.getFieldSort()
                && op instanceof Function
                && term.arity() == 0
                && op.name().toString().contains("::$")
                || op == heapLDT.getArr();
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        String name = term.op().name().toString();
        String smtName = "field_" + name;

        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        Operator op = term.op();

        if (op == heapLDT.getArr()) {
            return trans.handleAsFunctionCall("arr", term);
        }

        if(op == heapLDT.getCreated()) {
            // java.lang.Object::$<created> is a special symbol handled already in Heap
            trans.addFromSnippets(smtName);
        }

        if (!trans.isKnownSymbol(smtName)) {
            Map<String, Object> state = trans.getTranslationState();
            Integer curVal = (Integer) state.getOrDefault(CONSTANT_COUNTER_PROPERTY, -2);

            trans.addFromSnippets("fieldIdentifier");

            trans.addDeclaration(new SExpr("declare-const", smtName, "U"));

            trans.addAxiom(new SExpr("assert",
                    new SExpr("=",
                            new SExpr("fieldIdentifier", smtName),
                            new SExpr(curVal.toString()))));

            state.put(CONSTANT_COUNTER_PROPERTY, curVal - 1);
            trans.addKnownSymbol(smtName);
        }
        return new SExpr(smtName);
    }

}
