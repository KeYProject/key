package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import org.key_project.util.collection.ImmutableArray;

/**
 * This visitor collects the definition of a variable introduced in a proof leaf by Z3's
 * skolemization rule (sk).
 *
 * @author Wolfram Pfeifer
 */
class SkolemCollector extends SMTProofBaseVisitor<Void> {
    private final SMTReplayer smtReplayer;
    private final String skVariable;
    private final Services services;

    public SkolemCollector(SMTReplayer smtReplayer, String skVariable, Services services) {
        this.smtReplayer = smtReplayer;
        this.skVariable = skVariable;
        this.services = services;
    }

    @Override
    public Void visitProofsexpr(SMTProofParser.ProofsexprContext ctx) {
        if (ctx.rulename != null && ctx.rulename.getText().equals("sk")) {
            // found sk rule -> create ifEx/epsilon term for skolem variable

            SMTProofParser.ProofsexprContext succ = ctx.proofsexpr(0);
            // inside of the sk rule there is always an equisatisfiability Noproofterm
            SMTProofParser.NoprooftermContext eqSat = succ.noproofterm();
            if (!eqSat.func.getText().equals("~")) {
                throw new IllegalStateException("Found sk rule that does not contain ~ top level!");
            }
            SMTProofParser.NoprooftermContext ex = eqSat.noproofterm(1);

            DefCollector collector = new DefCollector(smtReplayer, services);
            Term term = collector.visit(ex);

            if (term.op() == Quantifier.EX) {
                // TODO: check that we have the right variable (sk term may contain other skolem symbols as well!)

                // TODO: how to get a collision free var name?
                Name varName = new Name(skVariable);
                // TODO: currently ifEx supports integer sort only!
                IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
                QuantifiableVariable qv = new LogicVariable(varName, intLDT.targetSort());

                // as condition, we take the formula under the exists quantifier and replace the bound variable by qv
                QuantifiableVariable exBoundVar = term.boundVars().get(0);
                Term cond = ReplayTools.replace(exBoundVar, qv, term.sub(0), services);
                TermBuilder tb = services.getTermBuilder();
                Term _then = tb.var(qv);
                // TODO: error value
                Term _else = tb.zTerm(-1);    // error value: -1
                Term def = tb.ifEx(qv, cond, _then, _else);
                // add to map
                smtReplayer.putSkolemSymbol(skVariable, def);
                //smtReplayer.translationToTermMap.putIfAbsent(skVariable, def);
                smtReplayer.addTranslationToTerm(skVariable, def);
            } else if (term.op() == Junctor.NOT
                && term.sub(0).op() == Quantifier.ALL) {

                Term all = term.sub(0);
                Name varName = new Name(skVariable);
                IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
                QuantifiableVariable qv = new LogicVariable(varName, intLDT.targetSort());
                QuantifiableVariable allBoundVar = all.boundVars().get(0);
                Term cond = ReplayTools.replace(allBoundVar, qv, all.sub(0), services);
                TermBuilder tb = services.getTermBuilder();
                Term _then = tb.var(qv);
                // TODO: error value
                Term _else = tb.zTerm(-1);
                Term def = tb.ifEx(qv, cond, _then, _else);
                smtReplayer.putSkolemSymbol(skVariable, def);
                smtReplayer.addTranslationToTerm(skVariable, def);
            } else {
                throw new IllegalStateException("Invalid sk rule found (no existential quantifier)!");
            }
            return null;
        }
        // descend into rules that are not sk
        return super.visitProofsexpr(ctx);
    }
}
