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

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.Vector;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.intermediate.AppNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BuiltInAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.JoinAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.JoinPartnerAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.TacletAppIntermediate;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.Pair;

/**
 * Parses a KeY proof file into an intermediate representation. The parsed
 * intermediate result can be processed by {@link IntermediateProofReplayer}.
 * This approach is more flexible than direct parsing; for instance, it is
 * capable of dealing with join rule applications.
 * <p>
 * 
 * The returned intermediate proof closely resembles the structure of the parsed
 * proof file. Specifically, branch nodes are explicitly stored and, as in the
 * proof file, have exactly one child (or zero in the case of an empty proof).
 * The first node, that is also the main returned result, is a branch node with
 * the identifier "dummy ID" that is present in every proof.
 * <p>
 * 
 * Example for parsed intermediate proof:
 * <p>
 * 
 * <pre>
 * BranchNodeIntermediate "dummy ID"
 * - AppNodeIntermediate
 * - AppNodeIntermediate
 * - ...
 * - AppNodeIntermediate
 *   + BranchNodeIntermediate "x > 0"
 *     > AppNodeIntermediate
 *     > ...
 *   + BranchNodeIntermediate "x <= 0"
 *     > AppNodeIntermediate
 *     > ...
 * </pre>
 * <p>
 * 
 * Note that the last open goal in an unfinished proof is not represented by a
 * node in the intermediate representation (since no rule has been applied on
 * the goal yet).
 * <p>
 * 
 * The results of the parser may be obtained by calling {@link #getResult()}.
 * 
 * @author Dominic Scheurer
 */
public class IntermediatePresentationProofFileParser implements
        IProofFileParser {

    /* + The proof object for storing meta information */
    private Proof proof = null;

    /* + Open Branches */
    private Stack<NodeIntermediate> stack = new Stack<NodeIntermediate>();

    /* + State Information */
    private RuleInformation ruleInfo = null;

    /* + State information that is returned after parsing */
    private BranchNodeIntermediate root = null; // the "dummy ID" branch
    private NodeIntermediate currNode = null;

    /**
     * @param proof
     *            Proof object for storing meta information about the parsed
     *            proof.
     */
    public IntermediatePresentationProofFileParser(Proof proof) {
        this.proof = proof;
        this.currNode = this.root;
    }

    @Override
    public void beginExpr(ProofElementID eid, String str) {
        switch (eid) {
        case BRANCH: // branch
        {
            final BranchNodeIntermediate newNode = new BranchNodeIntermediate(
                    str);

            if (root == null) {
                root = newNode;
                currNode = newNode;
                stack.push(newNode);
            }
            else {
                stack.push(currNode);
                currNode.addChild(newNode);
                currNode = newNode;
            }
        }
            break;

        case RULE: // rule (taclet)
        {
            final AppNodeIntermediate newNode = new AppNodeIntermediate();
            currNode.addChild(newNode);
            currNode = newNode;
        }

            ruleInfo = new TacletInformation(str);
            break;

        case FORMULA: // formula
            final int formula = Integer.parseInt(str);
            if (insideBuiltinIfInsts()) {
                ((BuiltinRuleInformation) ruleInfo).currIfInstFormula = formula;
            }
            else {
                ruleInfo.currFormula = formula;
            }
            break;

        case TERM: // term
            final PosInTerm pos = PosInTerm.parseReverseString(str);
            if (insideBuiltinIfInsts()) {
                ((BuiltinRuleInformation) ruleInfo).currIfInstPosInTerm = pos;
            }
            else {
                ruleInfo.currPosInTerm = pos;
            }
            break;

        case INSTANTIATION: // inst
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            if (tacletInfo.loadedInsts == null) {
                tacletInfo.loadedInsts = new LinkedList<String>();
            }
            tacletInfo.loadedInsts.add(str);
        }
            break;

        case RULESET: // heuristics
            break;

        case ASSUMES_FORMULA_IN_SEQUENT: // ifseqformula
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            tacletInfo.ifSeqFormulaList = tacletInfo.ifSeqFormulaList
                    .append(str);
        }
            break;

        case ASSUMES_FORMULA_DIRECT: // ifdirectformula
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            tacletInfo.ifDirectFormulaList = tacletInfo.ifDirectFormulaList
                    .append(str);
        }
            break;

        case KeY_USER: // UserLog
            if (proof.userLog == null) {
                proof.userLog = new Vector<String>();
            }
            proof.userLog.add(str);
            break;

        case KeY_VERSION: // Version log
            if (proof.keyVersionLog == null) {
                proof.keyVersionLog = new Vector<String>();
            }
            proof.keyVersionLog.add(str);
            break;

        case KeY_SETTINGS: // ProofSettings
            loadPreferences(str);
            break;

        case BUILT_IN_RULE: // BuiltIn rules
        {
            final AppNodeIntermediate newNode = new AppNodeIntermediate();
            currNode.addChild(newNode);
            currNode = newNode;
        }

            ruleInfo = new BuiltinRuleInformation(str);
            break;

        case CONTRACT: // contract
            ((BuiltinRuleInformation) ruleInfo).currContract = str;
            break;

        case ASSUMES_INST_BUILT_IN: // ifInst (for built in rules)
            BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;

            if (builtinInfo.builtinIfInsts == null) {
                builtinInfo.builtinIfInsts = ImmutableSLList
                        .<Pair<Integer, PosInTerm>> nil();
            }
            builtinInfo.currIfInstFormula = 0;
            builtinInfo.currIfInstPosInTerm = PosInTerm.getTopLevel();
            break;

        case NEW_NAMES: // newnames
            final String[] newNames = str.split(",");
            ruleInfo.currNewNames = ImmutableSLList.<Name> nil();
            for (int in = 0; in < newNames.length; in++) {
                ruleInfo.currNewNames = ruleInfo.currNewNames.append(new Name(
                        newNames[in]));
            }
            break;

        case AUTOMODE_TIME: // autoModeTime
            try {
                proof.addAutoModeTime(Long.parseLong(str));
            }
            catch (NumberFormatException e) {
                /* ignore */
            }
            break;

        case JOIN_PROCEDURE: // join procedure
            ((BuiltinRuleInformation) ruleInfo).currJoinProc = str;
            break;

        case NUMBER_JOIN_PARTNERS: // number of join partners
            ((BuiltinRuleInformation) ruleInfo).currNrPartners = Integer
                    .parseInt(str);
            break;

        case JOIN_NODE: // corresponding join node id
            ((BuiltinRuleInformation) ruleInfo).currCorrespondingJoinNodeId = Integer
                    .parseInt(str);
            break;

        case JOIN_ID: // join node id
            ((BuiltinRuleInformation) ruleInfo).currJoinNodeId = Integer
                    .parseInt(str);
            break;
            
        case JOIN_DIST_FORMULA: // distinguishing formula for joins
            ((BuiltinRuleInformation) ruleInfo).currDistFormula = str;
            break;
            
        default:
            break;
        }

    }

    @Override
    public void endExpr(ProofElementID eid, int lineNr) {
        switch (eid) {
        case BRANCH: // branch
            currNode = stack.pop();
            break;

        case USER_INTERACTION: // userinteraction
            if (currNode != null) {
                ((AppNodeIntermediate) currNode)
                        .setInteractiveRuleApplication(true);
            }
            break;

        case RULE: // rule (taclet)
            ((AppNodeIntermediate) currNode)
                    .setIntermediateRuleApp(constructTacletApp());
            ((AppNodeIntermediate) currNode).getIntermediateRuleApp()
                    .setLineNr(lineNr);
            break;

        case BUILT_IN_RULE: // BuiltIn rules
            ((AppNodeIntermediate) currNode)
                    .setIntermediateRuleApp(constructBuiltInApp());
            ((AppNodeIntermediate) currNode).getIntermediateRuleApp()
                    .setLineNr(lineNr);
            break;

        case ASSUMES_INST_BUILT_IN: // ifInst (for built in rules)
            BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;
            builtinInfo.builtinIfInsts = builtinInfo.builtinIfInsts
                    .append(new Pair<Integer, PosInTerm>(
                            builtinInfo.currIfInstFormula,
                            builtinInfo.currIfInstPosInTerm));
            break;

        default:
            break;
        }
    }

    /**
     * @return The results of the parsing procedure.
     */
    public Result getResult() {
        return new Result(getErrors(), getStatus(), root);
    }

    @Override
    public String getStatus() {
        return "";
    }

    @Override
    public List<Throwable> getErrors() {
        return new LinkedList<Throwable>();
    }

    /**
     * @return The parsed intermediate representation in form of the top level
     *         branch node (the "dummy ID" branch).
     */
    public BranchNodeIntermediate getParsedResult() {
        return root;
    }

    /**
     * @return An intermediate taclet application generated from previously
     *         parsed information.
     */
    private TacletAppIntermediate constructTacletApp() {
        TacletInformation tacletInfo = (TacletInformation) ruleInfo;
        return new TacletAppIntermediate(tacletInfo.currRuleName,
                new Pair<Integer, PosInTerm>(tacletInfo.currFormula,
                        tacletInfo.currPosInTerm), tacletInfo.loadedInsts,
                tacletInfo.ifSeqFormulaList, tacletInfo.ifDirectFormulaList,
                tacletInfo.currNewNames);
    }

    /**
     * @return An intermediate built-in rule application generated from
     *         previously parsed information.
     */
    private BuiltInAppIntermediate constructBuiltInApp() {
        BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;
        BuiltInAppIntermediate result = null;

        if (builtinInfo.currRuleName.equals("JoinRule")) {
            result = new JoinAppIntermediate(builtinInfo.currRuleName,
                    new Pair<Integer, PosInTerm>(builtinInfo.currFormula,
                            builtinInfo.currPosInTerm),
                    builtinInfo.currJoinNodeId, builtinInfo.currJoinProc,
                    builtinInfo.currNrPartners, builtinInfo.currNewNames,
                    builtinInfo.currDistFormula);
        }
        else if (builtinInfo.currRuleName.equals("CloseAfterJoin")) {
            result = new JoinPartnerAppIntermediate(builtinInfo.currRuleName,
                    new Pair<Integer, PosInTerm>(builtinInfo.currFormula,
                            builtinInfo.currPosInTerm),
                    builtinInfo.currCorrespondingJoinNodeId,
                    builtinInfo.currNewNames);
        }
        else {
            result = new BuiltInAppIntermediate(builtinInfo.currRuleName,
                    new Pair<Integer, PosInTerm>(builtinInfo.currFormula,
                            builtinInfo.currPosInTerm),
                    builtinInfo.currContract, builtinInfo.builtinIfInsts,
                    builtinInfo.currNewNames);
        }

        return result;
    }

    /**
     * Loads proof settings.
     *
     * @param preferences
     *            The preferences to load.
     */
    private void loadPreferences(String preferences) {
        final ProofSettings proofSettings = ProofSettings.DEFAULT_SETTINGS;
        proofSettings.loadSettingsFromString(preferences);
    }

    /**
     * @return True iff we are currently parsing a built-in rule and are inside
     *         an if-insts sub expression.
     */
    private boolean insideBuiltinIfInsts() {
        return ruleInfo.isBuiltinInfo()
                && ((BuiltinRuleInformation) ruleInfo).builtinIfInsts != null;
    }

    /**
     * General information about taclet and built-in rule applications.
     *
     * @author Dominic Scheurer
     */
    private static abstract class RuleInformation {
        /* + General Information */
        protected String currRuleName = null;
        protected int currFormula = 0;
        protected PosInTerm currPosInTerm = PosInTerm.getTopLevel();
        protected ImmutableList<Name> currNewNames = null;

        public RuleInformation(String ruleName) {
            this.currRuleName = ruleName;
        }

        public boolean isBuiltinInfo() {
            return this instanceof BuiltinRuleInformation;
        }
    }

    /**
     * Information about taclet applications.
     *
     * @author Dominic Scheurer
     */
    private static class TacletInformation extends RuleInformation {
        /* + Taclet Information */
        protected LinkedList<String> loadedInsts = null;
        protected ImmutableList<String> ifSeqFormulaList = ImmutableSLList
                .<String> nil();
        protected ImmutableList<String> ifDirectFormulaList = ImmutableSLList
                .<String> nil();

        public TacletInformation(String ruleName) {
            super(ruleName);
        }
    }

    /**
     * Information about built-in rule applications.
     *
     * @author Dominic Scheurer
     */
    private static class BuiltinRuleInformation extends RuleInformation {
        /* + Built-In Formula Information */
        protected ImmutableList<Pair<Integer, PosInTerm>> builtinIfInsts;
        protected int currIfInstFormula;
        protected PosInTerm currIfInstPosInTerm;
        /* > Method Contract */
        protected String currContract = null;
        /* > Join Rule */
        protected String currJoinProc = null;
        protected int currNrPartners = 0;
        protected int currCorrespondingJoinNodeId = 0;
        protected int currJoinNodeId = 0;
        protected String currDistFormula = null;

        public BuiltinRuleInformation(String ruleName) {
            super(ruleName);
        }
    }

    /**
     * Simple structure comprising the results of the parser.
     *
     * @author Dominic Scheurer
     */
    static class Result {
        private List<Throwable> errors;
        private String status;
        private BranchNodeIntermediate parsedResult = null;

        public Result(List<Throwable> errors, String status,
                BranchNodeIntermediate parsedResult) {
            this.errors = errors;
            this.status = status;
            this.parsedResult = parsedResult;
        }

        public List<Throwable> getErrors() {
            return errors;
        }

        public String getStatus() {
            return status;
        }

        public BranchNodeIntermediate getParsedResult() {
            return parsedResult;
        }

    }

}
