package de.uka.ilkd.key.macros.scripts;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 *
 * instantiate var=a occ=2 with="a_8" hide
 *
 * instantiate formula="\forall int a; phi(a)" with="a_8"
 *
 * @author mulbrich
 *
 */
public class InstantiateCommand extends AbstractCommand {

    private static class Parameters {
        Term formula;
        String var;
        int occ = 1;
        boolean hide;
        public Term with;
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args) throws ScriptException, InterruptedException {

        Parameters params = parseParameters(proof, args);

        if((params.var == null) == (params.formula == null)) {
            throw new ScriptException("One of 'var' or 'formula' must be specified");
        }

        Goal goal = getFirstOpenGoal(proof);

        if(params.var != null) {
            computeFormula(params, goal);
        }

        assert params.formula != null;

        TacletApp theApp = findTacletApp(proof, params);
        if(theApp == null) {
            throw new ScriptException("No taclet applicatin found");
        }

        SchemaVariable sv = theApp.uninstantiatedVars().iterator().next();

        theApp = theApp.addInstantiation(sv, params.with, true /*???*/, proof.getServices());

        theApp = theApp.tryToInstantiate(proof.getServices());

        Goal g = getFirstOpenGoal(proof);
        g.apply(theApp);
    }

    private TacletApp findTacletApp(Proof proof, Parameters p)
            throws ScriptException {

        ImmutableList<TacletApp> allApps = findAllTacletApps(proof, p);
        TacletApp matchingApp = filterList(p, allApps);

        if(matchingApp == null) {
            throw new ScriptException("No matching applications.");
        }

        return matchingApp;
    }

    private ImmutableList<TacletApp> findAllTacletApps(Proof proof, Parameters p)
            throws ScriptException {

        String rulename;
        if(p.formula.op() == Quantifier.ALL) {
            rulename = "allLeft" + (p.hide ? "Hide" : "");
        } else {
            rulename = "exRight" + (p.hide ? "Hide" : "");
        }

        Services services = proof.getServices();
        TacletFilter filter = new TacletNameFilter(rulename);
        Goal g = getFirstOpenGoal(proof);
        RuleAppIndex index = g.ruleAppIndex ();
        index.autoModeStopped ();

        ImmutableList<TacletApp> allApps = ImmutableSLList.nil();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            if(p.formula != null && !sf.formula().equals(p.formula)) {
                continue;
            }
            allApps = allApps.append(
                    index.getTacletAppAtAndBelow(filter,
                            new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                            services));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if(p.formula != null && !sf.formula().equals(p.formula)) {
                continue;
            }
            allApps = allApps.append(
                    index.getTacletAppAtAndBelow(filter,
                            new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                            services));
        }

        return allApps;
    }
    /*
     * Filter those apps from a list that are according to the parameters.
     */
    private TacletApp filterList(Parameters p, ImmutableList<TacletApp> list) {
        List<TacletApp> matchingApps = new ArrayList<TacletApp>();
        for (TacletApp tacletApp : list) {
            if(tacletApp instanceof PosTacletApp) {
                PosTacletApp pta = (PosTacletApp) tacletApp;
                if(pta.posInOccurrence().subTerm().equals(p.formula)) {
                    return pta;
                }
            }
        }
        return null;
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



    private void computeFormula(Parameters params, Goal goal) throws ScriptException {
        Node n = goal.node();
        Sequent seq = n.sequent();
        int occ = params.occ;
        for(SequentFormula form : seq.antecedent().asList()) {
            Term term = form.formula();
            if(term.op() == Quantifier.ALL) {
                String varName = term.boundVars().get(0).name().toString();
                if(params.var.equals(varName)) {
                    occ --;
                    if(occ == 0) {
                        params.formula = term;
                        return;
                    }
                }
            }
        }

        for(SequentFormula form : seq.succedent().asList()) {
            Term term = form.formula();
            if(term.op() == Quantifier.EX) {
                String varName = term.boundVars().get(0).name().toString();
                if(params.var.equals(varName)) {
                    occ --;
                    if(occ == 0) {
                        params.formula = term;
                        return;
                    }
                }
            }
        }

        throw new ScriptException("Variable '" + params.var +
                "' has no occurrence no. '" + params.occ + "'.");
    }

    private Parameters parseParameters(Proof proof, Map<String, String> args)
            throws ScriptException {
        Parameters params = new Parameters();

        //
        // var="a"
        params.var = args.get("var");

        //
        // formula="toplevel formula in which it appears"
        // formula="\forall int a; phi(a)"
        String formStr = args.get("formula");
        if(formStr != null) {
            try {
                params.formula = toTerm(proof, formStr, Sort.FORMULA);
            } catch (Exception e) {
                throw new ScriptException(e);
            }
        }

        //
        // occurrence number;
        String occStr = args.get("occ");
        if(occStr != null) {
            try {
                params.occ = Integer.parseInt(occStr);
            } catch (NumberFormatException e) {
                throw new ScriptException(e);
            }
        }

        //
        // instantiation
        String withStr = args.get("with");
        if(withStr != null) {
            try {
                params.with = toTerm(proof, withStr, null);
            } catch (ParserException e) {
                throw new ScriptException(e);
            }
        } else {
            throw new ScriptException("'with' must be specified");
        }

        //
        // hide
        params.hide = args.containsKey("#2") && args.get("#2").equals("hide");


        return params;
    }

    @Override
    public String getName() {
        return "instantiate";
    }

}
