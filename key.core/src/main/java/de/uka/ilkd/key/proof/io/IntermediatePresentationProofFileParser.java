/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.intermediate.*;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Parses a KeY proof file into an intermediate representation. The parsed intermediate result can
 * be processed by {@link IntermediateProofReplayer}. This approach is more flexible than direct
 * parsing; for instance, it is capable of dealing with merge rule applications.
 * <p>
 *
 * The returned intermediate proof closely resembles the structure of the parsed proof file.
 * Specifically, branch nodes are explicitly stored and, as in the proof file, have exactly one
 * child (or zero in the case of an empty proof). The first node, that is also the main returned
 * result, is a branch node with the identifier "dummy ID" that is present in every proof.
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
 * Note that the last open goal in an unfinished proof is not represented by a node in the
 * intermediate representation (since no rule has been applied on the goal yet).
 * <p>
 *
 * The results of the parser may be obtained by calling {@link #getResult()}.
 *
 * @author Dominic Scheurer
 */
public class IntermediatePresentationProofFileParser implements IProofFileParser {

    /* + The proof object for storing meta information */
    private Proof proof = null;

    /* + Open Branches */
    private final ArrayDeque<NodeIntermediate> stack = new ArrayDeque<>();

    /* + State Information */
    private RuleInformation ruleInfo = null;

    /* + State information that is returned after parsing */
    private BranchNodeIntermediate root = null; // the "dummy ID" branch
    private NodeIntermediate currNode = null;
    private final LinkedList<Throwable> errors = new LinkedList<>();

    /**
     * @param proof Proof object for storing meta information about the parsed proof.
     */
    public IntermediatePresentationProofFileParser(Proof proof) {
        this.proof = proof;
        this.currNode = this.root;
    }

    @Override
    @SuppressWarnings("unchecked")
    public void beginExpr(ProofElementID eid, String str) {
        switch (eid) {
        case BRANCH: // branch
        {
            final BranchNodeIntermediate newNode = new BranchNodeIntermediate(str);

            if (root == null) {
                root = newNode;
                currNode = newNode;
                stack.push(newNode);
            } else {
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
            } else {
                ruleInfo.currFormula = formula;
            }
            break;

        case TERM: // term
            final PosInTerm pos = PosInTerm.parseReverseString(str);
            if (insideBuiltinIfInsts()) {
                ((BuiltinRuleInformation) ruleInfo).currIfInstPosInTerm = pos;
            } else {
                ruleInfo.currPosInTerm = pos;
            }
            break;

        case INSTANTIATION: // inst
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            if (tacletInfo.loadedInsts == null) {
                tacletInfo.loadedInsts = new LinkedList<>();
            }
            tacletInfo.loadedInsts.add(str);
        }
            break;

        case RULESET: // heuristics
            break;

        case ASSUMES_FORMULA_IN_SEQUENT: // ifseqformula
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            tacletInfo.ifSeqFormulaList = tacletInfo.ifSeqFormulaList.append(str);
        }
            break;

        case ASSUMES_FORMULA_DIRECT: // ifdirectformula
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            tacletInfo.ifDirectFormulaList = tacletInfo.ifDirectFormulaList.append(str);
        }
            break;

        case KeY_USER: // UserLog
            if (proof.userLog == null) {
                proof.userLog = new ArrayList<>();
            }
            proof.userLog.add(str);
            break;

        case KeY_VERSION: // Version log
            if (proof.keyVersionLog == null) {
                proof.keyVersionLog = new ArrayList<>();
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

        case MODALITY:
            // (additional information which can be used in external tools such as proof management)
            ((BuiltinRuleInformation) ruleInfo).currContractModality = str;
            break;

        case ASSUMES_INST_BUILT_IN: // ifInst (for built in rules)
            BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;

            if (builtinInfo.builtinIfInsts == null) {
                builtinInfo.builtinIfInsts = ImmutableSLList.nil();
            }
            builtinInfo.currIfInstFormula = 0;
            builtinInfo.currIfInstPosInTerm = PosInTerm.getTopLevel();
            break;

        case NEW_NAMES: // newnames
            final String[] newNames = str.split(",");
            ruleInfo.currNewNames = ImmutableSLList.nil();
            for (String newName : newNames) {
                ruleInfo.currNewNames = ruleInfo.currNewNames.append(new Name(newName));
            }
            break;

        case AUTOMODE_TIME: // autoModeTime
            try {
                proof.addAutoModeTime(Long.parseLong(str));
            } catch (NumberFormatException e) {
                /* ignore */
            }
            break;

        case MERGE_PROCEDURE: // merge procedure
            ((BuiltinRuleInformation) ruleInfo).currMergeProc = str;
            break;

        case NUMBER_MERGE_PARTNERS: // number of merge partners
            ((BuiltinRuleInformation) ruleInfo).currNrPartners = Integer.parseInt(str);
            break;

        case MERGE_NODE: // corresponding merge node id
            ((BuiltinRuleInformation) ruleInfo).currCorrespondingMergeNodeId =
                Integer.parseInt(str);
            break;

        case MERGE_ID: // merge node id
            ((BuiltinRuleInformation) ruleInfo).currMergeNodeId = Integer.parseInt(str);
            break;

        case MERGE_DIST_FORMULA: // distinguishing formula for merges
            ((BuiltinRuleInformation) ruleInfo).currDistFormula = str;
            break;

        case MERGE_PREDICATE_ABSTRACTION_LATTICE_TYPE: // type of predicate
                                                       // abstraction lattice
            try {
                ((BuiltinRuleInformation) ruleInfo).currPredAbstraLatticeType =
                    (Class<? extends AbstractPredicateAbstractionLattice>) Class.forName(str);
            } catch (ClassNotFoundException e) {
                errors.add(e);
            }
            break;

        case MERGE_ABSTRACTION_PREDICATES:
            ((BuiltinRuleInformation) ruleInfo).currAbstractionPredicates = str;
            break;

        case MERGE_USER_CHOICES:
            ((BuiltinRuleInformation) ruleInfo).currUserChoices = str;
            break;

        case NOTES:
            ruleInfo.notes = str;
            if (currNode != null) {
                ((AppNodeIntermediate) currNode).setNotes(ruleInfo.notes);
            }
            break;
        case SOLVERTYPE:
            ((BuiltinRuleInformation) ruleInfo).solver = str;
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
                ((AppNodeIntermediate) currNode).setInteractiveRuleApplication(true);
            }
            break;

        case PROOF_SCRIPT: // proof script node
            if (currNode != null) {
                ((AppNodeIntermediate) currNode).setScriptRuleApplication(true);
            }
            break;

        case RULE: // rule (taclet)
            ((AppNodeIntermediate) currNode).setIntermediateRuleApp(constructTacletApp());
            ((AppNodeIntermediate) currNode).getIntermediateRuleApp().setLineNr(lineNr);
            break;

        case BUILT_IN_RULE: // BuiltIn rules
            ((AppNodeIntermediate) currNode).setIntermediateRuleApp(constructBuiltInApp());
            ((AppNodeIntermediate) currNode).getIntermediateRuleApp().setLineNr(lineNr);
            break;

        case ASSUMES_INST_BUILT_IN: // ifInst (for built in rules)
            BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;
            builtinInfo.builtinIfInsts =
                builtinInfo.builtinIfInsts.append(new Pair<>(
                    builtinInfo.currIfInstFormula, builtinInfo.currIfInstPosInTerm));
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
        return errors;
    }

    /**
     * @return The parsed intermediate representation in form of the top level branch node (the
     *         "dummy ID" branch).
     */
    public BranchNodeIntermediate getParsedResult() {
        return root;
    }

    /**
     * @return An intermediate taclet application generated from previously parsed information.
     */
    private TacletAppIntermediate constructTacletApp() {
        TacletInformation tacletInfo = (TacletInformation) ruleInfo;
        return new TacletAppIntermediate(tacletInfo.currRuleName,
            new Pair<>(tacletInfo.currFormula, tacletInfo.currPosInTerm),
            tacletInfo.loadedInsts, tacletInfo.ifSeqFormulaList, tacletInfo.ifDirectFormulaList,
            tacletInfo.currNewNames);
    }

    /**
     * @return An intermediate built-in rule application generated from previously parsed
     *         information.
     */
    private BuiltInAppIntermediate constructBuiltInApp() {
        BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;
        BuiltInAppIntermediate result = null;

        if (builtinInfo.currRuleName.equals("MergeRule")) {
            result =
                new MergeAppIntermediate(builtinInfo.currRuleName,
                    new Pair<>(builtinInfo.currFormula,
                        builtinInfo.currPosInTerm),
                    builtinInfo.currMergeNodeId, builtinInfo.currMergeProc,
                    builtinInfo.currNrPartners, builtinInfo.currNewNames,
                    builtinInfo.currDistFormula, builtinInfo.currPredAbstraLatticeType,
                    builtinInfo.currAbstractionPredicates, builtinInfo.currUserChoices);
        } else if (builtinInfo.currRuleName.equals("CloseAfterMerge")) {
            result = new MergePartnerAppIntermediate(builtinInfo.currRuleName,
                new Pair<>(builtinInfo.currFormula, builtinInfo.currPosInTerm),
                builtinInfo.currCorrespondingMergeNodeId, builtinInfo.currNewNames);
        } else if (builtinInfo.currRuleName.equals("SMTRule")) {
            result = new SMTAppIntermediate(builtinInfo.currRuleName,
                new Pair<>(builtinInfo.currFormula, builtinInfo.currPosInTerm),
                builtinInfo.solver);
        } else {
            result = new BuiltInAppIntermediate(builtinInfo.currRuleName,
                new Pair<>(builtinInfo.currFormula, builtinInfo.currPosInTerm),
                builtinInfo.currContract, builtinInfo.currContractModality,
                builtinInfo.builtinIfInsts, builtinInfo.currNewNames);
        }

        return result;
    }

    /**
     * Loads proof settings.
     *
     * @param preferences The preferences to load.
     */
    private void loadPreferences(String preferences) {
        final ProofSettings proofSettings = ProofSettings.DEFAULT_SETTINGS;
        proofSettings.loadSettingsFromString(preferences);
    }

    /**
     * @return True iff we are currently parsing a built-in rule and are inside an if-insts sub
     *         expression.
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
        protected String notes = null;

        public RuleInformation(String ruleName) {
            this.currRuleName = ruleName.trim();
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
        protected ImmutableList<String> ifSeqFormulaList = ImmutableSLList.nil();
        protected ImmutableList<String> ifDirectFormulaList = ImmutableSLList.nil();

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
        protected String currContractModality = null;
        /* > Merge Rule */
        protected String currMergeProc = null;
        protected int currNrPartners = 0;
        protected int currCorrespondingMergeNodeId = 0;
        protected int currMergeNodeId = 0;
        protected String currDistFormula = null;
        protected Class<? extends AbstractPredicateAbstractionLattice> currPredAbstraLatticeType =
            null;
        protected String currAbstractionPredicates = null;
        protected String currUserChoices = null;
        protected String solver;

        public BuiltinRuleInformation(String ruleName) {
            super(ruleName);
        }
    }

    /**
     * Simple structure comprising the results of the parser.
     *
     * @author Dominic Scheurer
     */
    public static class Result {
        private final List<Throwable> errors;
        private final String status;
        private BranchNodeIntermediate parsedResult = null;

        public Result(List<Throwable> errors, String status, BranchNodeIntermediate parsedResult) {
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
