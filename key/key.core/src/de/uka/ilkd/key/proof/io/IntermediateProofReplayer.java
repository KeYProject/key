// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.DefaultProofFileParser.AppConstructionException;
import de.uka.ilkd.key.proof.io.DefaultProofFileParser.BuiltInConstructionException;
import de.uka.ilkd.key.proof.io.DefaultProofFileParser.SkipSMTRuleException;
import de.uka.ilkd.key.proof.io.intermediate.AppNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BuiltInAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.JoinAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.JoinPartnerAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.TacletAppIntermediate;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.util.Pair;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class IntermediateProofReplayer {

    private static final String ERROR_LOADING_PROOF_LINE = "Error loading proof.\n";
    private static final String NOT_APPLICABLE = " not available or not applicable in this context.";

    private final AbstractProblemLoader loader;
    private Proof proof = null;
    
    private List<Throwable> errors = new LinkedList<Throwable>();
    private String status = "";

    private LinkedList<Pair<Node, NodeIntermediate>> queue = new LinkedList<Pair<Node, NodeIntermediate>>();

    private HashMap<Integer, HashSet<Pair<Node, NodeIntermediate>>> joinPartnerNodes = new HashMap<Integer, HashSet<Pair<Node, NodeIntermediate>>>();
    
    /**
     * a value == 1 means the current branch is ignored; a value > 1 means that
     * the "skipBranch - 1" parent branch of the current branch is ignored. a
     * value == 0 means that no branch is ignored
     */
    private int skipBranch = 0; //TODO: Implement skipBranch feature
    
    private Goal currGoal = null;

    /**
     * TODO: Document.
     *
     * @param loader
     * @param proof
     * @param intermediate
     */
    public IntermediateProofReplayer(AbstractProblemLoader loader, Proof proof,
            BranchNodeIntermediate intermediate) {
        this.proof = proof;
        this.loader = loader;

        queue.addFirst(new Pair<Node, NodeIntermediate>(proof.root(),
                intermediate));
    }
    
    /**
     * @return the lastSelectedGoal
     */
    public Goal getLastSelectedGoal() {
        return currGoal;
    }

    public void replay() {
        while (!queue.isEmpty()) {
            final Pair<Node, NodeIntermediate> currentP = queue.pollFirst();
            final Node currNode = currentP.first;
            currGoal = proof.getGoal(currNode);

            
            if (currentP.second instanceof BranchNodeIntermediate) {
                queue.addFirst(new Pair<Node, NodeIntermediate>(currNode, currentP.second.getChildren().get(0)));
            }
            else if (currentP.second instanceof AppNodeIntermediate) {
                AppNodeIntermediate currInterm = (AppNodeIntermediate) currentP.second;

                if (currInterm.getIntermediateRuleApp() instanceof TacletAppIntermediate) {
                    TacletAppIntermediate appInterm = (TacletAppIntermediate) currInterm
                            .getIntermediateRuleApp();
                    
                    try {
                        currGoal.apply(constructApp(appInterm, currGoal));
                        
                        int i = 0;
                        Iterator<Node> children = currNode.childrenIterator();
                        while (!currGoal.node().isClosed() && children.hasNext()) {
                            Node child = children.next();
                            queue.addLast(new Pair<Node, NodeIntermediate>(child, currInterm.getChildren().get(i++)));
                        }
                    }
                    catch (Exception e) {
                        skipBranch = 1;
                        reportError(ERROR_LOADING_PROOF_LINE + "Goal " + currGoal.node().serialNr() + ", rule "
                                + appInterm.getTacletName() + NOT_APPLICABLE, e);
                    }
                    catch (AssertionError e) {
                        skipBranch = 1;
                        reportError(ERROR_LOADING_PROOF_LINE + "Goal " + currGoal.node().serialNr() + ", rule "
                                + appInterm.getTacletName() + NOT_APPLICABLE, e);
                    }
                    
                }
                else if (currInterm.getIntermediateRuleApp() instanceof BuiltInAppIntermediate) {
                    BuiltInAppIntermediate appInterm = (BuiltInAppIntermediate) currInterm
                            .getIntermediateRuleApp();
                    
                    if (appInterm instanceof JoinAppIntermediate) {
                        // TODO
                    }
                    else if (appInterm instanceof JoinPartnerAppIntermediate) {
                        // TODO
                    }
                    else {
                        try {
                            IBuiltInRuleApp app = constructBuiltinApp(appInterm, currGoal);
                            if (!app.complete()) {
                                app = app.tryToInstantiate(currGoal);
                            }
                            currGoal.apply(app);
                            
                            int i = 0;
                            Iterator<Node> children = currNode.childrenIterator();
                            while (children.hasNext()) {
                                Node child = children.next();
                                queue.addLast(new Pair<Node, NodeIntermediate>(child, currInterm.getChildren().get(i++)));
                            }
                        }
                        catch (SkipSMTRuleException e) {
                            // silently continue; status will be reported via
                            // polling
                        }
                        catch (BuiltInConstructionException e) {
                            skipBranch = 1;
                            reportError(ERROR_LOADING_PROOF_LINE + "Goal " + currGoal.node().serialNr()
                                    + ", rule " + appInterm.getRuleName() + NOT_APPLICABLE,
                                    e);
                        }
                        catch (RuntimeException e) {
                            skipBranch = 1;
                            reportError(ERROR_LOADING_PROOF_LINE + "Goal " + currGoal.node().serialNr()
                                    + ", rule " + appInterm.getRuleName() + NOT_APPLICABLE,
                                    e);
                        }
                        catch (AssertionError e) {
                            skipBranch = 1;
                            reportError(ERROR_LOADING_PROOF_LINE + "Goal " + currGoal.node().serialNr()
                                    + ", rule " + appInterm.getRuleName() + NOT_APPLICABLE,
                                    e);
                        }
                    }
                }
            }
        }
    }

    /**
     * Communicates a non-fatal condition to the caller. Empty string means
     * everything is OK. The message will be displayed to the user in the GUI
     * after the proof has been parsed.
     */
    public String getStatus() {
        return status;
    }

    /**
     * TODO: Document.
     *
     * @return
     */
    public Collection<Throwable> getErrors() {
        return errors;
    }

    /**
     * TODO: Document.
     *
     * @return
     * @throws AppConstructionException
     */
    private TacletApp constructApp(TacletAppIntermediate currInterm, Goal currGoal) throws AppConstructionException {
        
        final String tacletName = currInterm.getTacletName();
        final int currFormula = currInterm.getPosInfo().first;
        final PosInTerm currPosInTerm = currInterm.getPosInfo().second;
        
        TacletApp ourApp = null;
        PosInOccurrence pos = null;

        Taclet t = proof.getInitConfig().lookupActiveTaclet(
                new Name(tacletName));
        if (t == null) {
            ourApp = currGoal.indexOfTaclets().lookup(tacletName);
        }
        else {
            ourApp = NoPosTacletApp.createNoPosTacletApp(t);
        }
        Services services = proof.getServices();

        if (currFormula != 0) { // otherwise we have no pos
            pos = PosInOccurrence.findInSequent(currGoal.sequent(),
                    currFormula, currPosInTerm);
            // System.err.print("Want to apply "+currTacletName+" at "+currGoal);
            // this is copied from TermTacletAppIndex :-/

            ourApp = ((NoPosTacletApp) ourApp).matchFind(pos, services);
            ourApp = ourApp.setPosInOccurrence(pos, services);
        }

        ourApp = constructInsts(ourApp, currGoal, currInterm.getInsts(), services);

        ImmutableList<IfFormulaInstantiation> ifFormulaList = ImmutableSLList.nil();
        for (String ifFormulaStr : currInterm.getIfSeqFormulaList()) {
            Sequent seq = currGoal.sequent();
            ifFormulaList = ifFormulaList.append(new IfFormulaInstSeq(seq,
                    Integer.parseInt(ifFormulaStr)));
        }
        for (String ifFormulaStr : currInterm.getIfDirectFormulaList()) {
            ifFormulaList = ifFormulaList.append(new IfFormulaInstDirect(
                    new SequentFormula(DefaultProofFileParser.parseTerm(ifFormulaStr, proof))));
        }
        
        ourApp = ourApp.setIfFormulaInstantiations(ifFormulaList, services);

        if (!ourApp.complete()) {
            ourApp = ourApp.tryToInstantiate(proof.getServices());
        }

        return ourApp;
    }
    
    /**
     * TODO: Document.
     *
     * @param currInterm
     * @param currGoal
     * @return
     * @throws SkipSMTRuleException
     * @throws BuiltInConstructionException
     */
    private IBuiltInRuleApp constructBuiltinApp(BuiltInAppIntermediate currInterm, Goal currGoal) throws SkipSMTRuleException,
            BuiltInConstructionException {

        final String ruleName = currInterm.getRuleName();
        final int currFormula = currInterm.getPosInfo().first;
        final PosInTerm currPosInTerm = currInterm.getPosInfo().second;
        
        Contract currContract = null;
        ImmutableList<PosInOccurrence> builtinIfInsts = null;
        
        // Load contracts, if applicable
        if (currInterm.getContract() != null) {
            currContract = proof.getServices().getSpecificationRepository()
                    .getContractByName(currInterm.getContract());
            if (currContract == null) {
                final ProblemLoaderException e = new ProblemLoaderException(
                        loader, "Error loading proof: contract \"" + currInterm.getContract()
                                + "\" not found.");
                reportError(ERROR_LOADING_PROOF_LINE + ", goal "
                        + currGoal.node().serialNr() + ", rule "
                        + ruleName + NOT_APPLICABLE, e);
            }
        }
        
        // Load ifInsts, if applicable
        if (currInterm.getBuiltInIfInsts() != null) {
            for (Pair<Integer, PosInTerm> ifInstP : currInterm.getBuiltInIfInsts()) {
                final int currIfInstFormula = ifInstP.first;
                final PosInTerm currIfInstPosInTerm = ifInstP.second;
                
                try {
                    final PosInOccurrence ifInst = PosInOccurrence.findInSequent(
                            currGoal.sequent(), currIfInstFormula,
                            currIfInstPosInTerm);
                    builtinIfInsts = builtinIfInsts.append(ifInst);
                }
                catch (RuntimeException e) {
                    skipBranch = 1;
                    reportError(ERROR_LOADING_PROOF_LINE + "Goal " + currGoal.node().serialNr() + ", rule "
                            + ruleName + NOT_APPLICABLE, e);
                }
                catch (AssertionError e) {
                    skipBranch = 1;
                    reportError(ERROR_LOADING_PROOF_LINE + "Goal " + currGoal.node().serialNr() + ", rule "
                            + ruleName + NOT_APPLICABLE, e);
                }
            }
        }
        
        if (RuleAppSMT.rule.name().toString().equals(ruleName)) {
            boolean error = false;
            final SMTProblem smtProblem = new SMTProblem(currGoal);
            try {
                SMTSettings settings = new SMTSettings(proof.getSettings()
                        .getSMTSettings(),
                        ProofIndependentSettings.DEFAULT_INSTANCE
                                .getSMTSettings(), proof);
                SolverLauncher launcher = new SolverLauncher(settings);
                // launcher.addListener(new SolverListener(settings, proof));
                SolverTypeCollection active = ProofIndependentSettings.DEFAULT_INSTANCE
                        .getSMTSettings().computeActiveSolverUnion();
                ArrayList<SMTProblem> problems = new ArrayList<SMTProblem>();
                problems.add(smtProblem);
                launcher.launch(active.getTypes(), problems,
                        proof.getServices());
            }
            catch (Exception e) {
                error = true;
            }
            if (error
                    || smtProblem.getFinalResult().isValid() != ThreeValuedTruth.VALID) {
                status = "Your proof has been loaded, but SMT solvers have not been run";
                throw new SkipSMTRuleException();
            }
            else {
                return RuleAppSMT.rule.createApp(null, proof.getServices());
            }
        }

        IBuiltInRuleApp ourApp = null;
        PosInOccurrence pos = null;

        if (currFormula != 0) { // otherwise we have no pos
            try {
                pos = PosInOccurrence.findInSequent(currGoal.sequent(),
                        currFormula, currPosInTerm);
            }
            catch (RuntimeException e) {
                throw new BuiltInConstructionException(e);
            }
        }

        if (currContract != null) {
            AbstractContractRuleApp contractApp = null;

            BuiltInRule useContractRule;
            if (currContract instanceof OperationContract) {
                useContractRule = UseOperationContractRule.INSTANCE;
                contractApp = (((UseOperationContractRule) useContractRule)
                        .createApp(pos)).setContract(currContract);
            }
            else {
                useContractRule = UseDependencyContractRule.INSTANCE;
                contractApp = (((UseDependencyContractRule) useContractRule)
                        .createApp(pos)).setContract(currContract);
            }

            if (contractApp.check(currGoal.proof().getServices()) == null) {
                throw new BuiltInConstructionException(
                        "Cannot apply contract: " + currContract);
            }
            else {
                ourApp = contractApp;
            }

            currContract = null;
            if (builtinIfInsts != null) {
                ourApp = ourApp.setIfInsts(builtinIfInsts);
                builtinIfInsts = null;
            }
            return ourApp;
        }

        final ImmutableSet<IBuiltInRuleApp> ruleApps = collectAppsForRule(
                ruleName, currGoal, pos);
        if (ruleApps.size() != 1) {
            if (ruleApps.size() < 1) {
                throw new BuiltInConstructionException(ruleName
                        + " is missing. Most probably the binary "
                        + "for this built-in rule is not in your path or "
                        + "you do not have the permission to execute it.");
            }
            else {
                throw new BuiltInConstructionException(ruleName
                        + ": found " + ruleApps.size()
                        + " applications. Don't know what to do !\n" + "@ "
                        + pos);
            }
        }
        ourApp = ruleApps.iterator().next();
        builtinIfInsts = null;
        return ourApp;
    }

    /**
     * TODO: Document.
     *
     * @param string
     * @param e
     */
    private void reportError(String string, Throwable e) {
        status = "Errors while reading the proof. Not all branches could be load successfully.";
        errors.add(new ProblemLoaderException(loader, string, e));
    }

    /**
     * TODO: Document.
     *
     * @param ruleName
     * @param g
     * @param pos
     * @return
     */
    private ImmutableSet<IBuiltInRuleApp> collectAppsForRule(String ruleName,
            Goal g, PosInOccurrence pos) {
        ImmutableSet<IBuiltInRuleApp> result = DefaultImmutableSet
                .<IBuiltInRuleApp> nil();

        for (final IBuiltInRuleApp app : g.ruleAppIndex().getBuiltInRules(g,
                pos)) {
            if (app.rule().name().toString().equals(ruleName)) {
                result = result.add(app);
            }
        }

        return result;
    }

    /**
     * TODO: Document.
     *
     * @param app
     * @param services
     * @return
     */
    private TacletApp constructInsts(TacletApp app, Goal currGoal, LinkedList<String> loadedInsts, Services services) {
        if (loadedInsts == null)
            return app;
        ImmutableSet<SchemaVariable> uninsts = app.uninstantiatedVars();

        // first pass: add variables
        Iterator<String> it = loadedInsts.iterator();
        while (it.hasNext()) {
            String s = it.next();
            int eq = s.indexOf('=');
            String varname = s.substring(0, eq);
            String value = s.substring(eq + 1, s.length());

            SchemaVariable sv = lookupName(uninsts, varname);
            if (sv == null) {
                // throw new IllegalStateException(
                // varname+" from \n"+loadedInsts+"\n is not in\n"+uninsts);
                System.err.println(varname + " from " + app.rule().name()
                        + " is not in uninsts");
                continue;
            }

            if (sv instanceof VariableSV) {
                app = DefaultProofFileParser.parseSV1(app, sv, value, services);
            }
        }

        // second pass: add everything else
        uninsts = app.uninstantiatedVars();
        it = loadedInsts.iterator();
        while (it.hasNext()) {
            String s = it.next();
            int eq = s.indexOf('=');
            String varname = s.substring(0, eq);
            String value = s.substring(eq + 1, s.length());
            SchemaVariable sv = lookupName(uninsts, varname);
            if (sv == null) {
                continue;
            }
            app = DefaultProofFileParser.parseSV2(app, sv, value, currGoal);
        }

        return app;
    }
    
    /**
     * TODO: Document.
     *
     * @param set
     * @param name
     * @return
     */
    private SchemaVariable lookupName(ImmutableSet<SchemaVariable> set,
            String name) {
        Iterator<SchemaVariable> it = set.iterator();
        while (it.hasNext()) {
            SchemaVariable v = it.next();
            if (v.name().toString().equals(name))
                return v;
        }
        return null; // handle this better!
    }
}
