package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;

public class ProofFinder extends DefaultBuilder {
    public ProofFinder(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    @Override
    public Object visitProof(KeYParser.ProofContext ctx) {
        return super.visitProof(ctx);
    }

    @Override
    public Object visitProofBody(KeYParser.ProofBodyContext ctx) {
        return super.visitProofBody(ctx);
    }

        /*
        @Override
        public Object visitProof(KeYParser.ProofContext ctx) {
            return super.visitProof(ctx);
        }

        @Override
        public Object visitProofBody(KeYParser.ProofBodyContext ctx) {
            return super.visitProofBody(ctx);
        }

        @Override
        public Object visitPseudosexpr(KeYParser.PseudosexprContext ctx) {
            proofElementId=expreid
                    (str = string_literal )?
                    { prl.beginExpr(proofElementId,str); }
            ( pseudosexpr[prl] )* )
            { prl.endExpr(proofElementId, stringLiteralLine); }
            return null;
        }

        @Override
        public IProofFileParser.ProofElementID visitExpreid(KeYParser.ExpreidContext ctx) {
            return prooflabel2tag.get(visitSimple_ident(ctx.simple_ident()));
        }*/

}
