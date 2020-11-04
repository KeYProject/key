package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

/**
 * Collection of static helper methods that are used in replay.
 *
 * @author Wolfram Pfeifer
 */
public final class ReplayTools {
    private ReplayTools() {
    }

    /**
     * Replaces a bound variable by another one in a term.
     * @param toReplace the variable to replace
     * @param with the new variable
     * @param in the Term to replace in
     * @param services Services needed to construct the new term
     * @return a new Term where every occurrence of the bound variable has been replaced with the
     *      new one
     */
    public static Term replace(QuantifiableVariable toReplace,
                               QuantifiableVariable with,
                               Term in,
                               Services services) {
        // using OpReplacer does not replace the QuantifiableVariables (due to missing equals
        // method?)
        // return OpReplacer.replace(tb.var(orig), tb.var(repl), t, tf);
        Operator newOp = in.op();
        if (newOp instanceof QuantifiableVariable
            && equalsOp((QuantifiableVariable) newOp, toReplace)) {
            newOp = with;
        }

        Term[] newTerms = new Term[in.subs().size()];
        for (int i = 0; i < newTerms.length; i++) {
            newTerms[i] = replace(toReplace, with, in.subs().get(i), services);
        }
        // note: bound vars must be bound in new term again!
        return services.getTermFactory().createTerm(newOp, newTerms, in.boundVars(), null);
    }

    /**
     * Gets the original text of the given context, i.e. the text as it was specified in the input.
     * In contrast to ctx.getText(), this includes the whitespace.
     * @param ctx the context to construct the original text
     * @return the original text of ctx with whitespace
     */
    public static String getOriginalText(ParserRuleContext ctx) {
        if (ctx.start == null || ctx.start.getStartIndex() < 0
            || ctx.stop == null || ctx.stop.getStopIndex() < 0) {
            // fallback
            return ctx.getText();
        }
        int start = ctx.start.getStartIndex();
        int end = ctx.stop.getStopIndex();
        return ctx.start.getInputStream().getText(Interval.of(start, end));
    }

    // TODO: replace by real equals method in QuantifiableVariable
    public static boolean equalsOp(QuantifiableVariable a, QuantifiableVariable b) {
        return a.name().equals(b.name()) && a.sort().equals(b.sort());
    }
}
