package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

public class SumProdHandler implements SMTHandler {

    private Services services;
    Function bsumOp, bprodOp;

    //key is the term to identify the bsum, value is the name used for that function.
    private final HashMap<Term, SExpr> usedBsumTerms = new LinkedHashMap();

    //key is the term to identify the bprod, value is the name used for that function.
    private final HashMap<Term, SExpr> usedBprodTerms = new LinkedHashMap();

    @Override
    public void init(Services services) {
        this.services = services;
        bsumOp = services.getTypeConverter().getIntegerLDT().getBsum();
        bprodOp = services.getTypeConverter().getIntegerLDT().getBprod();
    }

    @Override
    public boolean canHandle(Term term) {
        Operator op = term.op();
        boolean isSum = op == bsumOp;
        boolean isProd = op == bprodOp;
        return isSum || isProd;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        Operator op = term.op();
        if (op == bsumOp) {
            for (Term t : usedBsumTerms.keySet()) {
                if (t.equalsModRenaming(term)) {
                    return usedBsumTerms.get(t);
                }
            }
            List<SExpr> exprs = new LinkedList<>();
            exprs.add(trans.translate(term.sub(0)));
            exprs.add(trans.coerce(trans.translate(term.sub(1)), SExpr.Type.INT));
            String s = String.valueOf(usedBsumTerms.size());
            trans.addDeclaration(bsumOrProdDecl("bsum", s));
            SExpr ret = new SExpr("bsum" + s, SExpr.Type.INT, exprs);
            usedBsumTerms.put(term, ret);
            return ret;
        } else if (op == bprodOp) {
            for (Term t : usedBprodTerms.keySet()) {
                if (t.equalsModRenaming(term)) {
                    return usedBprodTerms.get(t);
                }
            }
            List<SExpr> exprs = new LinkedList<>();
            exprs.add(trans.translate(term.sub(0)));
            exprs.add(trans.coerce(trans.translate(term.sub(1)), SExpr.Type.INT));
            String s = String.valueOf(usedBprodTerms.size());
            trans.addDeclaration(bsumOrProdDecl("bprod", s));
            SExpr ret = new SExpr("bprod" + s, SExpr.Type.INT, exprs);
            usedBprodTerms.put(term, ret);
            return ret;
        } else { //unreachable
            return new SExpr("ERROR");
        }
    }

    SExpr bsumOrProdDecl(String fun, String number) {
        return new SExpr("declare-fun", SExpr.Type.INT,
                new SExpr(fun + number),
                new SExpr(new SExpr("Int"), new SExpr("Int")), new SExpr("Int"));
    }
}
