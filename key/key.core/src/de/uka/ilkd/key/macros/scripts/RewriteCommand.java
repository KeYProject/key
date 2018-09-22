package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.TacletApp;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * This class provides the command <code>rewrite</code>.
 * <p>
 * This command takes two parameters. A term to find, and a term
 * as the substitutent. Parameter class is {@link RewriteCommand.Parameters}.
 * <p>
 *
 * <p>Usage:
 * <pre>
 *     rewrite find="x+y" replace="y+x"; //(mulbrich script syntax)
 *     rewrite find=`y+x` replace=`y+x`; //(psdbg)
 * </pre>
 * </p>
 *
 * @author lulong, grebing, weigl
 */
public class RewriteCommand extends AbstractCommand<RewriteCommand.Parameters> {
    /**
     * Constructs this rewrite command.
     */
    public RewriteCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "rewrite";
    }


    @Override
    public Parameters evaluateArguments(EngineState state,
                                        Map<String, String> arguments) throws Exception {
        return state.getValueInjector()
                .inject(this, new Parameters(), arguments);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl,
                        Parameters args, EngineState state)
            throws ScriptException, InterruptedException {
        Proof proof = state.getProof();
        assert proof != null;

        //get all Taclets
        ImmutableList<TacletApp> allApps = findAllTacletApps(args, state);

        //filter only taclets on find, also sets allReplSucc to false
        // if one replacement isn't successful
        //TODO: failPosInOcc only needed for different cut structures
        List<PosInOccurrence> failposInOccs = findAndExecReplacement(args, allApps, state);

        if (failposInOccs.size() >= 1) {

            System.out.println("Cut needed");
            CutCommand cut = new CutCommand();
            CutCommand.Parameters param = new CutCommand.Parameters();
            param.formula = args.replace;

            cut.execute(uiControl, param, state);
            System.out.println("After final cut:" + state.getFirstOpenGoal().sequent());


        }

    }

    /**
     * get aLl TacletApps
     */
    private ImmutableList<TacletApp> findAllTacletApps(Parameters p,
                                                       EngineState state) throws ScriptException {
        Services services = state.getProof().getServices();
        TacletFilter filter = TacletFilter.TRUE;
        Goal g = state.getFirstOpenGoal();
        RuleAppIndex index = g.ruleAppIndex();
        index.autoModeStopped();

        ImmutableList<TacletApp> allApps = ImmutableSLList.nil();
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
    //TODO: probably void, except if we want the failed PosInOccs
    //FIXME: should be rewritten into smaller pieces!
    private List<PosInOccurrence> findAndExecReplacement(
            Parameters p, ImmutableList<TacletApp> list, EngineState state) {
        //List of PosInOcc that haven't been  succ replaced
        List<PosInOccurrence> failposInOccs = new ArrayList<>();
        System.out.println("Size = 0:" + failposInOccs.size());

        //List of PosInOcc that succ replaced
        List<PosInOccurrence> succposInOccs = new ArrayList<>();

        for (TacletApp tacletApp : list) {
            if (tacletApp instanceof PosTacletApp) {
                PosTacletApp pta = (PosTacletApp) tacletApp;
                if (pta.taclet() instanceof RewriteTaclet) {
                    if (pta.taclet().displayName().equals("cut_direct")) {
                        continue;
                    }
                    if (pta.posInOccurrence().subTerm().equals(p.find) && pta.complete()) {
                        //System.out.println("________________________________________");
                        //System.out.println("Tacletapp an der Stelle: "
                        // + tacletApp.posInOccurrence());
                        //System.out.println("Tacletname an der Stelle: "
                        // + pta.taclet().displayName());
                        //if Term already succ replaced, the skip
                        if (succposInOccs.contains(pta.posInOccurrence())) {
                            System.out.println("Term already successfully replaced.");
                            continue;
                        }

                        // TODO: if taclet transforms find to replace then execute
                        // and add to list, else null

                        try {
                            System.out.println("Term NOT already successfully replaced.");
                            Goal goalold = state.getFirstOpenGoal();

                            //check the rewritten term
                            RewriteTaclet rw = (RewriteTaclet) pta.taclet();
                            if (pta.complete()) {
                                //for top level formulas -> TODO what about subterm replacements
                                SequentFormula rewriteResult = rw.getExecutor()
                                        .getRewriteResult(goalold, null,
                                                goalold.proof().getServices(), pta);
                                System.out.println("Rewrite Result =" + rewriteResult.toString());
                                if (rewriteResult.formula().equals(p.replace) ||
                                        getTermAtPos(rewriteResult, pta.posInOccurrence())
                                                .equals(p.replace)) {
                                    failposInOccs.remove(pta.posInOccurrence());
                                    succposInOccs.add(pta.posInOccurrence());
                                    System.out.println("Sucessful Replacement, applying rule app");
                                    goalold.apply(pta);
                                    break;
                                } else {
                                    System.out.println("Unsucessful Replacement & " +
                                            "already in failed list");
                                }
                            }
                            /*//TODO: nicht immer an der gleichen pio
                            if (pta.posInOccurrence().subTerm()
                                    .equals(p.replace)) {

                                failposInOccs.remove(pta.posInOccurrence());
                                succposInOccs.add(pta.posInOccurrence());
                                System.out.println("Sucessful Replacement");
                            } else {
                                if (!failposInOccs.contains(pta.posInOccurrence())) {
                                    System.out.println("Unsucessful "+
                                    "Replacement & add to failed list:");
                                    failposInOccs.add(pta.posInOccurrence());
                                    state.setGoal(goalold);
                                } else {
                                    //prune
                                    System.out.println("Unsucessful Replacement
                                    & already in failed list");
                                    state.setGoal(goalold);
                                }
                            }*/
                        } catch (Exception e) {
                            if (!failposInOccs.contains(pta.posInOccurrence())) {
                                failposInOccs.add(pta.posInOccurrence());
                            }
                            //FIXME not good design, no output on console
                            System.out.println("TacletApp not applicable");
                            e.printStackTrace();
                        }
                    }
                }
            }
        }
        System.out.println("[End of findExec] Size = ? :" + failposInOccs.size());
        return failposInOccs;
    }

    private Term getTermAtPos(SequentFormula sf, PosInOccurrence pio) {
        if (pio.isTopLevel()) {
            return sf.formula();

        } else {
            PosInTerm pit = pio.posInTerm();
            return getSubTerm(sf.formula(), pit.iterator());
        }

    }

    /**
     * ...?
     *
     * @param t
     * @param pit
     * @return
     */
    private Term getSubTerm(Term t, IntIterator pit) {
        if (pit.hasNext()) {
            int i = pit.next();
            return getSubTerm(t.sub(i), pit);
        } else {
            return t;
        }
    }

    /**
     * Parameters for the {@link RewriteCommand}
     *
     * @author luong, grebing, weigl
     */
    public static class Parameters {
        /**
         * Term, which should be replaced
         */
        @Option(value = "find")
        public Term find;
        /**
         * Substitutent
         */
        @Option(value = "replace")
        public Term replace;
        /**
         * Formula, where to find {@see find}.
         */
        @Option(value = "formula", required = false)
        public Term formula;
    }
}

