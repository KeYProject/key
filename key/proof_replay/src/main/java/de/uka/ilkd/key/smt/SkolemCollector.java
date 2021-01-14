package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.RuleNode;

import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import static de.uka.ilkd.key.smt.SMTProofParser.*;

/**
 * This visitor collects the definition of a skolem constant/function introduced in a proof leaf by
 * Z3's skolemization rule (sk).
 *
 * @author Wolfram Pfeifer
 */
class SkolemCollector extends SMTProofBaseVisitor<Void> {
    private final SMTReplayer smtReplayer;
    private final String skVariable;
    private final Services services;
    private final SMTSymbolRetranslator retranslator;

    /** used to store the resulting epsilon term. May be changed if lambda bound variables have to
     * be replaced! */
    private Term foundDef = null;

    /** used to store skolem function params (lambda bound variables; have to be replaced later
     * depending on the context where the skolem function is used). Empty for skolem constants! */
    private final List<NoprooftermContext> params = new LinkedList<>();

    /** used to carry variables bound by a quantifier into nested contexts */
    private final Deque<QuantifiableVariable> boundVars = new LinkedList<>();

    public SkolemCollector(SMTReplayer smtReplayer, String skVariable, Services services) {
        this.smtReplayer = smtReplayer;
        this.skVariable = skVariable;
        this.services = services;
        this.retranslator = new SMTSymbolRetranslator(services);
    }

    @Override
    public Void visitProofsexpr(ProofsexprContext ctx) {
        if (ctx.rulename != null && ctx.rulename.getText().equals("sk")) {
            // found sk rule -> create ifEx/epsilon term for skolem variable

            ProofsexprContext succ = ctx.proofsexpr(0);
            // inside of the sk rule there is always an equisatisfiability Noproofterm
            NoprooftermContext eqSat = succ.noproofterm();
            if (eqSat.func == null || !eqSat.func.getText().equals("~")) {
                throw new IllegalStateException("Found sk rule that does not contain ~ top level!");
            }
            // could be: ex x. phi(x) or !all x. phi(x)
            NoprooftermContext lhs = eqSat.noproofterm(1);
            NoprooftermContext rhs = eqSat.noproofterm(2);

            // unwrap let if necessary
            lhs = ReplayTools.ensureNoproofLookUp(lhs, smtReplayer);

            // look for position of bound variable in quantifier term
            String boundVarName;
            List<Integer> qvPos;
            // TODO: only case with single bound var handled
            if (lhs.quant != null && lhs.quant.getText().equals("exists")) {            // ex
                boundVarName = lhs.sorted_var(0).SYMBOL().getText();
                qvPos = ReplayTools.extractPosition(boundVarName, lhs.noproofterm(0));
            } else if (lhs.func != null && lhs.func.getText().equals("not")
                && lhs.noproofterm() != null && lhs.noproofterm().size() > 1) {

                // lhs.noproofterm(0) is 'not'
                NoprooftermContext lookup = ReplayTools.ensureNoproofLookUp(lhs.noproofterm(1),
                                                                            smtReplayer);
                if (lookup.quant != null && lookup.quant.getText().equals("forall")) {  // not all
                    boundVarName = lookup.sorted_var(0).SYMBOL().getText();
                    qvPos = ReplayTools.extractPosition(boundVarName, lookup.noproofterm(0));

                    // for skipping additional 'not' top level in rhs
                    qvPos.add(0, 1);
                } else {
                    throw new IllegalStateException("Collecting skolem symbol failed!");
                }
            } else {
                throw new IllegalStateException("Collecting skolem symbol failed!");
            }

            if (qvPos == null || qvPos.isEmpty()) {
                throw new IllegalStateException("Skolem symbol not found!");
            }

            // look for the skolem symbol name
            SMTProofParser.NoprooftermContext skSymbol = rhs;
            for (Integer i : qvPos) {
                skSymbol = ReplayTools.ensureNoproofLookUp(skSymbol, smtReplayer).noproofterm(i);
            }

            // abort if the name of the found skolem symbol does not equal the searched one
            if (skSymbol.func != null) {
                // case 1: searched variable is a skolem function: (var_a8!0 ...)
                // TODO: is it sufficient to only look at the function name?
                if (!skVariable.equals(skSymbol.func.getText())) {
                    return null;
                }
                // collect the list of params to be able to replace them later
                // (noproofterm(0) is skolem function name)
                for (int i = 1; i < skSymbol.noproofterm().size(); i++) {
                    params.add(skSymbol.noproofterm(i));
                }
            } else {
                // case 2: searched variable is a skolem constant: var_a8!0
                if (!skVariable.equals(skSymbol.getText())) {
                    // wrong sk rule -> abort
                    return null;
                }
            }

            DefCollector collector = new DefCollector(smtReplayer, boundVars, services);
            Term term = collector.visit(lhs);

            if (term.op() == Quantifier.EX) {
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

                foundDef = tb.ifEx(qv, cond, _then, _else);
                // IMPORTANT: the resulting term depends on whether we need it inside or outside
                //  of a lambda!
                //smtReplayer.putSkolemSymbol(skVariable, def);
                //smtReplayer.addTranslationToTerm(skVariable, def);
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
                foundDef = tb.ifEx(qv, cond, _then, _else);
                // IMPORTANT: the resulting term depends on whether we need it inside or outside
                //  of a lambda, we need to store the parameters (in the correct order) that have
                //  to be replaced depending on the context, where the skolem function is used!
                //smtReplayer.putSkolemSymbol(skVariable, def);
                //smtReplayer.addTranslationToTerm(skVariable, def);
            } else {
                throw new IllegalStateException("Invalid sk rule found!");
            }
            return null;
        } else if (ctx.rulename != null && ctx.rulename.getText().equals("lambda")) {

            for (int i = 0; i < ctx.sorted_var().size(); i++) {
                String varName = ctx.sorted_var(i).SYMBOL().getText();
                String fallbackSortName = ctx.sorted_var(i).sort().getText();
                Sort sort = ReplayTools.extractSort(services, retranslator, varName, ctx,
                    fallbackSortName);

                QuantifiableVariable qv = retranslator.translateOrCreateLogicVariable(varName,
                                                                                      sort);
                boundVars.push(qv);
            }
            visit(ctx.proofsexpr(0));
            for (int i = 0; i < ctx.sorted_var().size(); i++) {
                QuantifiableVariable qv = boundVars.pop();
                Term varTerm = services.getTermBuilder().var(qv);
                TermFactory tf = services.getTermFactory();
                // since we are outside of the lambda now, we have to use the corresponding variable
                // bound by a quantifier
                //foundDef = OpReplacer.replace(varTerm, , foundDef, tf);
            }
            return null;
        }
        // descend into rules that are not sk
        return super.visitProofsexpr(ctx);
    }

    @Override
    public Void visitIdentifier(IdentifierContext ctx) {
        ParserRuleContext letDef = smtReplayer.getSymbolDef(ctx.getText(), ctx);
        if (letDef != null) {
            visit(letDef);
        }
        return super.visitIdentifier(ctx);
    }

    @Override
    protected boolean shouldVisitNextChild(RuleNode node, Void currentResult) {
        return foundDef == null;
    }

    private Term getDefaultValueTerm(Sort targetSort) {
        Function anyf = services.getNamespaces().functions().lookup("any::defaultValue");
        SortDependingFunction genericF = (SortDependingFunction) anyf;
        Function targetF = genericF.getInstanceFor(targetSort, services);
        return services.getTermBuilder().func(targetF);
    }

    /**
     * Returns the epsilon term as found by the SkolemCollector. If the searched symbol is a skolem
     * function, this term still contains free variables. These can be be obtained via
     * {@link #getParams()} and have to be replaced dependent on the context where the skolem
     * function is used.
     * @return the definition found by the SkolemCollector
     */
    public Term getRawTerm() {
        return foundDef;
    }

    /**
     * If the symbol the SkolemCollector searched is a skolem function, the returned list contains
     * the parameters the function had while collecting (these are free variables in the Term
     * obtained by {@link #getRawTerm()}). The parameters have to be replaced dependent on the
     * context where the skolem function shall be used.
     * @return the parameters of the skolem function
     */
    public List<NoprooftermContext> getParams() {
        return params;
    }
}
