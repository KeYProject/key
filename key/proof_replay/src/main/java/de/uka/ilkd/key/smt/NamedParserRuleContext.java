package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * This class serves as adapter to be able to use Namespaces containing ParserRuleContext, since
 * Namespaces can only contain elements implementing the Named interface. One object of this class
 * holds the mapping from a symbol bound by let to its context.
 *
 * @author Wolfram Pfeifer
 */
public final class NamedParserRuleContext extends ParserRuleContext implements Named {
    /** the context corresponding to the symbol name */
    private final ParserRuleContext ctx;
    /** the name of the symbol */
    private final Name name;

    // TODO: idea: cache translation (for noproofterms)

    /**
     * Creates a new NamedParserRuleContext, i.e. a mapping from a symbol bound by let to its
     * context.
     * @param name the symbol name
     * @param ctx the corresponding context
     */
    public NamedParserRuleContext(String name, ParserRuleContext ctx) {
        this.name = new Name(name);
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
