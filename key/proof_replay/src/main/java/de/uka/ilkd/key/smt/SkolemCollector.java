package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Pair;

import java.util.Deque;
import java.util.LinkedList;

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
    private final SMTSymbolRetranslator retranslator;

    /** used to carry variables bound by a quantifier into nested contexts */
    private final Deque<QuantifiableVariable> boundVars = new LinkedList<>();

    /** used to carry symbols introduced by quant-intro rule (needed for replaying rules inside
     * the scope of a quant-intro/proof-bind/lambda) */
    private final Deque<Pair<QuantifiableVariable, Term>> skolemSymbols = new LinkedList<>();

    public SkolemCollector(SMTReplayer smtReplayer, String skVariable, Services services) {
        this.smtReplayer = smtReplayer;
        this.skVariable = skVariable;
        this.services = services;
        this.retranslator = new SMTSymbolRetranslator(services);
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
            // could be: ex x. phi(x) or !all x. phi(x)
            SMTProofParser.NoprooftermContext lhs = eqSat.noproofterm(1);

            DefCollector collector = new DefCollector(smtReplayer, boundVars, services);
            Term term = collector.visit(lhs);

            if (term.op() == Quantifier.EX) {
                // TODO: check that we have the right variable (sk term may contain other skolem symbols as well!)

                // TODO: how to get a collision free var name? do we need one?
                //services.getVariableNamer().getTemporaryNameProposal(skVariable)
                Name varName = new Name(skVariable);

                // as condition, we take the formula under the exists quantifier and replace the bound variable by qv
                QuantifiableVariable exBoundVar = term.boundVars().get(0);
                Sort targetSort = exBoundVar.sort();
                QuantifiableVariable qv = new LogicVariable(varName, targetSort);
                Term cond = ReplayTools.replace(exBoundVar, qv, term.sub(0), services);
                TermBuilder tb = services.getTermBuilder();
                Term _then = tb.var(qv);
                Term _else = getDefaultValueTerm(targetSort);

                Term def = tb.ifEx(qv, cond, _then, _else);
                // add to map
                smtReplayer.putSkolemSymbol(skVariable, def);
                smtReplayer.addTranslationToTerm(skVariable, def);
            } else if (term.op() == Junctor.NOT
                && term.sub(0).op() == Quantifier.ALL) {

                Term all = term.sub(0);
                Name varName = new Name(skVariable);
                QuantifiableVariable allBoundVar = all.boundVars().get(0);
                Sort targetSort = allBoundVar.sort();
                QuantifiableVariable qv = new LogicVariable(varName, targetSort);

                Term cond = all.sub(0);
                // we need an additional not

                // use TermFactory to ensure no simplification happens
                TermFactory tf = services.getTermFactory();
                cond = tf.createTerm(Junctor.NOT, cond);
                cond = ReplayTools.replace(allBoundVar, qv, cond, services);

                TermBuilder tb = services.getTermBuilder();
                Term _then = tb.var(qv);
                Term _else = getDefaultValueTerm(allBoundVar.sort());
                Term def = tb.ifEx(qv, cond, _then, _else);
                smtReplayer.putSkolemSymbol(skVariable, def);
                smtReplayer.addTranslationToTerm(skVariable, def);
            } else {
                throw new IllegalStateException("Invalid sk rule found!");
            }
            return null;
        } else if (ctx.rulename != null && ctx.rulename.getText().equals("lambda")) {

            for (int i = 0; i < ctx.sorted_var().size(); i++) {
                String varName = ctx.sorted_var(i).SYMBOL().getText();

                // we try to extract the sort from a typeguard (otherwise the sorts when creating
                // function terms will not match!)
                TypeguardSortCollector sortCollector = new TypeguardSortCollector(services, varName,
                                                                                  retranslator);
                Sort sort = sortCollector.visit(ctx.proofsexpr(0));
                if (sort == null) {
                    // if no typeguard is present we use the sort from declaration
                    String sortName = ctx.sorted_var(i).sort().getText();
                    sort = retranslator.translateSort(sortName);

                    if (sort == null) {
                        sort = Sort.ANY;    // fallback sort
                    }
                }

                QuantifiableVariable qv = retranslator.translateOrCreateLogicVariable(varName,
                                                                                      sort);
                boundVars.push(qv);
            }
            visit(ctx.proofsexpr(0));
            for (int i = 0; i < ctx.sorted_var().size(); i++) {
                boundVars.pop();
            }
            return null;
        }
        // descend into rules that are not sk
        return super.visitProofsexpr(ctx);
    }

    private Term getDefaultValueTerm(Sort targetSort) {
        Function anyf = services.getNamespaces().functions().lookup("any::defaultValue");
        SortDependingFunction genericF = (SortDependingFunction) anyf;
        Function targetF = genericF.getInstanceFor(targetSort, services);
        return services.getTermBuilder().func(targetF);
    }
}
