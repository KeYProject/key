package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.util.Position;
import de.uka.ilkd.key.util.Triple;

class ProofScriptFinder extends AbstractBuilder<Object> {
    private String proofScript;
    private Position position;

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        return null;
    }

    @Override
    public Object visitFile(KeYParser.FileContext ctx) {
        accept(ctx.decls());
        return null;
    }

    @Override
    public Triple<String, Integer, Integer> visitProofScript(KeYParser.ProofScriptContext ctx) {
        proofScript = ctx.ps.getText();
        position = Position.make(ctx.ps);
        return null;
    }

    public String getProofScript() {
        return proofScript;
    }

    public Position getPosition() {
        return position;
    }
}
