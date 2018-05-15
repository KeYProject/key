package de.uka.ilkd.key.smt.newsmt2;

import java.util.Collections;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class SelectHandler implements SMTHandler {

    private Services services;
    private Sort intType;
    private Sort boolType;

    @Override
    public void init(Services services) {
        this.services = services;
        NamespaceSet nss = services.getNamespaces();
        intType = nss.sorts().lookup("int");
        boolType = nss.sorts().lookup("boolean");
    }

    @Override
    public boolean canHandle(Term term) {
        return services.getTypeConverter().getHeapLDT().isSelectOp(term.op());
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortDependingFunction op = (SortDependingFunction) term.op();
        Sort dep = op.getSortDependingOn();
        String funName = dep.toString() + "::select";
        SExpr se1 = trans.translate(term.sub(0));
        SExpr se2 = trans.translate(term.sub(1));
        SExpr se3 = trans.translate(term.sub(2));

        if (!trans.isKnownSymbol(funName)) {
            trans.addAxiom(UninterpretedSymbolsHandler.funTypeAxiomFromTerm(term, funName, trans));

            SExpr signature = new SExpr(Collections.nCopies(3, new SExpr("U")));
            trans.addDeclaration(
                    new SExpr("declare-fun", new SExpr(funName), signature, new SExpr("U")));
            trans.addKnownSymbol(funName);
        }

        if (dep.equals(intType)) {
            return new SExpr(funName, Type.INT, se1, se2, se3);
        } else if (dep.equals(boolType)) {
            return new SExpr(funName, Type.BOOL, se1, se2, se3);
        } else {
            return new SExpr(funName, Type.UNIVERSE, se1, se2, se3);
        }
    }
}
