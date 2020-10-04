package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import org.antlr.v4.runtime.ParserRuleContext;

final class NamedParserRuleContext extends ParserRuleContext implements Named {
    private final ParserRuleContext ctx;
    private final Name name;

    // TODO: idea: cache translation (for noproofterms)

    public NamedParserRuleContext(String name, ParserRuleContext ctx) {
        this.name = new Name(name);
        this.ctx = ctx;
    }

    public NamedParserRuleContext(Name name, ParserRuleContext ctx) {
        this.name = name;
        this.ctx = ctx;
    }

    public ParserRuleContext getCtx() {
        return ctx;
    }

    @Override
    public Name name() {
        return name;
    }

    @Override
    public String toString() {
        return ctx.getText();
    }
}
