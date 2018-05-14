package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Rewrite Command
 * gets an ``find term and replace term
 * and replaces find terms on sequent with the
 *
 * Example:
 * rewrite find="t1" replace="t2"; (mulbrich script syntax)
 * rewrite find=`t1` replace=`t2`; (psdbg syntax)
 */

public class RewriteCommand extends AbstractCommand<RewriteCommand.Parameters>{
    public RewriteCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "rewrite";
    }


    @Override public Parameters evaluateArguments(EngineState state,
                                                              Map<String, String> arguments) throws Exception {
        Parameters p = state.getValueInjector()
                .inject(this, new Parameters(), arguments);
        return p;
    }

    @Override public void execute(AbstractUserInterfaceControl uiControl,
                                  Parameters args, EngineState state)
            throws ScriptException, InterruptedException {
        Proof proof = state.getProof();
        assert proof != null;

        ImmutableList<TacletApp> allApps = findAllTacletApps(args, state);

        List<PosInOccurrence> failposInOccs = findAndExecReplacement(args, allApps, state);

        //not all find terms successfully replaced -> apply cut
        if (failposInOccs.size() >= 1) {

           CutCommand cut = new CutCommand();
           CutCommand.Parameters param = new CutCommand.Parameters();
           param.formula = args.replace;

           cut.execute(uiControl, param, state);


        }

    }

    public static class Parameters {
        @Option(value = "find", required = true)
        public Term find;
        @Option(value = "replace", required = true)
        public Term replace;
        @Option(value = "formula", required = false)
        public Term formula;
    }

    /**
     * get all TacletApps
     */
    private ImmutableList<TacletApp> findAllTacletApps(Parameters p,
                                                       EngineState state) throws ScriptException {
        Services services = state.getProof().getServices();
        TacletFilter filter = TacletFilter.TRUE;
        Goal g = state.getFirstOpenGoal();
        RuleAppIndex index = g.ruleAppIndex();
        index.autoModeStopped();

        ImmutableList<TacletApp> allApps = ImmutableSLList.nil();

        //filter
        for (SequentFormula sf : g.node().sequent().antecedent()) {

            if (p.formula != null && !sf.formula()
                    .equalsModRenaming(p.formula)) {
                continue;
            }
            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                    services));
        }

        for (SequentFormula sf : g.node().sequent().succedent()) {
            if (p.formula != null && !sf.formula()
                    .equalsModRenaming(p.formula)) {
                continue;
            }
            allApps = allApps.append(index.getTacletAppAtAndBelow(filter,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                    services));
        }

        return allApps;
    }

 /**
 * Filter tacletapps: term = find && result = replace
 **/
 private List<PosInOccurrence> findAndExecReplacement(Parameters p,
                                       ImmutableList<TacletApp> list, EngineState state) {

        //List of PosInOccurrences of find terms that haven't been successfully replaced
        List<PosInOccurrence> failposInOccs = new ArrayList<PosInOccurrence>();

        //List ofPosInOccurrences of find terms that successfully replaced
        List<PosInOccurrence> succposInOccs = new ArrayList<PosInOccurrence>();

        //Find taclet that transforms find term to replace term, when applied on find term
        for (TacletApp tacletApp : list) {
            if (tacletApp instanceof PosTacletApp) {
                PosTacletApp pta = (PosTacletApp) tacletApp;
                if (pta.taclet() instanceof RewriteTaclet) {
                    if (pta.taclet().displayName().equals("cut_direct")) {
                        continue;
                    }
                    if (pta.posInOccurrence().subTerm().equals(p.find) && pta.complete()) {

                        //If term already succposInOccs , then skip
                        if (succposInOccs.contains(pta.posInOccurrence())) {
                            continue;
                        }

                        try {
                            Goal goal = state.getFirstOpenGoal();
                            RewriteTaclet rw = (RewriteTaclet) pta.taclet();
                            if(pta.complete()) {
                                SequentFormula rewriteResult = rw.getExecutor().getRewriteResult(goal, null, goal.proof().getServices(), pta);

                                //Transformed find term = replace term -> apply taclet
                                if(rewriteResult.formula().equals(p.replace) ||
                                        getTermAtPos(rewriteResult, pta.posInOccurrence()).equals(p.replace)){
                                    failposInOccs.remove(pta.posInOccurrence());
                                    succposInOccs.add(pta.posInOccurrence());
                                    goal.apply(pta);
                                    break;
                                }
                            }

                        } catch (Exception e) {
                            if (!failposInOccs.contains(pta.posInOccurrence())) {
                                failposInOccs.add(pta.posInOccurrence());
                            }

                            e.printStackTrace();
                            continue;
                        }


                    }
                }
            }
        }
        return failposInOccs;
    }

    /**
     * Calculates term at the PosInOccurrence pio
     * @param sf top-level formula
     * @param pio PosInOccurrence of the to be returned term
     * @return term at pio
     */
    public Term getTermAtPos(SequentFormula sf, PosInOccurrence pio){
        if(pio.isTopLevel()){
            return sf.formula();

        } else {
            PosInTerm pit = pio.posInTerm();
            Term t = getSubTerm(sf.formula(), pit.iterator());
            return t;
        }

    }

    /**
     * Calculates subterm of term t according to the given IntIterator
     * @param t Term
     * @param pit contains information of the position of subterm in t
     * @return subterm of t
     */
    public Term getSubTerm(Term t, IntIterator pit){
        if(pit.hasNext()) {
            int i = pit.next();
            return getSubTerm(t.sub(i), pit);
        } else {
            return t;
        }
    }




}

