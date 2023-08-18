/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * instantiate var=a occ=2 with="a_8" hide
 * <p>
 * instantiate formula="\forall int a; phi(a)" with="a_8"
 *
 * @author mulbrich
 */
public class InstantiateCommand extends AbstractCommand<InstantiateCommand.Parameters> {

    public InstantiateCommand() {
        super(Parameters.class);
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters params,
            EngineState state) throws ScriptException, InterruptedException {

        Goal goal = state.getFirstOpenAutomaticGoal();

        if ((params.var == null) == (params.formula == null)) {
            throw new ScriptException("One of 'var' or 'formula' must be specified");
        }

        if (params.var != null) {
            computeFormula(params, goal);
        }

        assert params.formula != null;

        TacletApp theApp = findTacletApp(params, state);
        if (theApp == null) {
            throw new ScriptException("No taclet application found");
        }

        SchemaVariable sv = theApp.uninstantiatedVars().iterator().next();

        theApp = theApp.addInstantiation(sv, params.with, true /* ??? */,
            state.getProof().getServices());

        theApp = theApp.tryToInstantiate(state.getProof().getServices());

        Goal g = state.getFirstOpenAutomaticGoal();
        g.apply(theApp);
    }

    private TacletApp findTacletApp(Parameters p, EngineState state) throws ScriptException {
        ImmutableList<TacletApp> allApps = findAllTacletApps(p, state);
        TacletApp matchingApp = filterList(p, allApps);

        if (matchingApp == null) {
            throw new ScriptException("No matching applications.");
        }

        return matchingApp;
    }

    private ImmutableList<TacletApp> findAllTacletApps(Parameters p, EngineState state)
            throws ScriptException {
        boolean hide = p.hide.equals("hide");


        String rulename;
        if (p.formula.op() == Quantifier.ALL) {
            rulename = "allLeft" + (hide ? "Hide" : "");
        } else {
            rulename = "exRight" + (hide ? "Hide" : "");
        }

        Proof proof = state.getProof();
        Services services = proof.getServices();
        TacletFilter filter = new TacletNameFilter(rulename);
        Goal g = state.getFirstOpenAutomaticGoal();
        RuleAppIndex index = g.ruleAppIndex();
        index.autoModeStopped();

        ImmutableList<TacletApp> allApps = ImmutableSLList.nil();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            if (p.formula != null && !sf.formula().equalsModRenaming(p.formula)) {
                continue;
            }
            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), true), services));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if (p.formula != null && !sf.formula().equalsModRenaming(p.formula)) {
                continue;
            }
            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), false), services));
        }

        return allApps;
    }

    /*
     * Filter those apps from a list that are according to the parameters.
     */
    private TacletApp filterList(Parameters p, ImmutableList<TacletApp> list) {
        for (TacletApp tacletApp : list) {
            if (tacletApp instanceof PosTacletApp) {
                PosTacletApp pta = (PosTacletApp) tacletApp;
                if (pta.posInOccurrence().subTerm().equalsModRenaming(p.formula)) {
                    return pta;
                }
            }
        }
        return null;
    }

    private void computeFormula(Parameters params, Goal goal) throws ScriptException {
        Node n = goal.node();
        Sequent seq = n.sequent();
        int occ = params.occ;
        for (SequentFormula form : seq.antecedent().asList()) {
            Term term = form.formula();
            Term stripped = stripUpdates(term);
            if (stripped.op() == Quantifier.ALL) {
                String varName = stripped.boundVars().get(0).name().toString();
                if (params.var.equals(varName)) {
                    occ--;
                    if (occ == 0) {
                        params.formula = term;
                        return;
                    }
                }
            }
        }

        for (SequentFormula form : seq.succedent().asList()) {
            Term term = form.formula();
            Term stripped = stripUpdates(term);
            if (stripped.op() == Quantifier.EX) {
                String varName = stripped.boundVars().get(0).name().toString();
                if (params.var.equals(varName)) {
                    occ--;
                    if (occ == 0) {
                        params.formula = term;
                        return;
                    }
                }
            }
        }

        throw new ScriptException(
            "Variable '" + params.var + "' has no occurrence no. '" + params.occ + "'.");
    }

    private Term stripUpdates(Term term) {
        while (term.op() == UpdateApplication.UPDATE_APPLICATION) {
            term = term.sub(1);
        }
        return term;
    }

    /*
     * public Parameters createArguments(EngineState state, Map<String, String> args) throws
     * ScriptException { Parameters params = new Parameters();
     *
     * // // var="a" params.var = args.get("var");
     *
     * // // formula="toplevel formula in which it appears" // formula="\forall int a; phi(a)"
     * String formStr = args.get("formula"); if (formStr != null) { try { params.formula =
     * toTerm(proof, state, formStr, Sort.FORMULA); } catch (Exception e) { throw new
     * ScriptException(e); } }
     *
     * // // occurrence number; String occStr = args.get("occ"); if (occStr != null) { try {
     * params.occ = Integer.parseInt(occStr); } catch (NumberFormatException e) { throw new
     * ScriptException(e); } }
     *
     * // // instantiation String withStr = args.get("with"); if (withStr != null) { try {
     * params.with = toTerm(proof, state, withStr, null); } catch (ParserException e) { throw new
     * ScriptException(e); } } else { throw new ScriptException("'with' must be specified"); }
     *
     * // // hide params.hide = args.containsKey("#2") && args.get("#2").equals("hide");
     *
     * return params; }
     */
    @Override
    public String getName() {
        return "instantiate";
    }

    /**
     *
     */
    public static class Parameters {
        @Option(value = "formula", required = false)
        public Term formula;
        @Option(value = "var", required = false)
        public String var;
        @Option(value = "occ", required = false)
        public int occ = 1;

        @Option(value = "#2", required = false)
        public String hide = "";

        @Option(value = "with", required = false)
        public Term with;
    }

    private static class TacletNameFilter extends TacletFilter {

        private final Name rulename;

        public TacletNameFilter(String rulename) {
            this.rulename = new Name(rulename);
        }

        @Override
        protected boolean filter(Taclet taclet) {
            return taclet.name().equals(rulename);
        }

    }

}
