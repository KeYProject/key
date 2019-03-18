package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.util.Map;

public class FieldConstantHandler implements SMTHandler {

    private Services services;

    @Override
    public void init(Services services) {
        this.services = services;
    }

    @Override
    // Review MU: I changed this to use any::cast since it would throw an exception
    // if applied to "null" terms.
    public boolean canHandle(Term term) {
        return term.sort() == services.getTypeConverter().getHeapLDT().getFieldSort()
                && term.op() instanceof Function
                && term.arity() == 0
                && term.op().name().toString().contains("::$");
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        String name = term.op().name().toString();
        String smtName = "field_" + name;

        if(term.op() == services.getTypeConverter().getHeapLDT().getCreated()) {
            // java.lang.Object::$<created> is a special symbol handled already in Heap
            trans.addFromSnippets(smtName);
        }

        if (!trans.isKnownSymbol(smtName)) {
            Map<String, Object> state = trans.getTranslationState();
            Integer curVal = (Integer) state.getOrDefault("fieldConstant.counter", -2);

            trans.addFromSnippets("fieldIdentifier");

            trans.addDeclaration(new SExpr("declare-const", smtName, "U"));

            trans.addAxiom(new SExpr("assert",
                    new SExpr("=",
                            new SExpr("fieldIdentifier", smtName),
                            new SExpr(curVal.toString()))));

            state.put("fieldConstant.counter", curVal - 1);
            trans.addKnownSymbol(smtName);
        }
        return new SExpr(smtName);
    }

}
