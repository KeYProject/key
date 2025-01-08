/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.util.ArrayDeque;
import java.util.LinkedList;
import java.util.List;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.io.intermediate.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;

public class IntermediatePresentationProofFileParser implements IProofFileParser {
    /* + The proof object for storing meta information */
    private final Proof proof;

    /* + Open Branches */
    private final ArrayDeque<NodeIntermediate> stack = new ArrayDeque<>();

    /* + State Information */
    private RuleInformation ruleInfo = null;

    /* + State information that is returned after parsing */
    private BranchNodeIntermediate root = null; // the "dummy ID" branch
    private NodeIntermediate currNode;
    private final LinkedList<Throwable> errors = new LinkedList<>();

    /**
     * @param proof Proof object for storing meta information about the parsed proof.
     */
    public IntermediatePresentationProofFileParser(Proof proof) {
        this.proof = proof;
    }

    @Override
    @SuppressWarnings("unchecked")
    public void beginExpr(IProofFileParser.ProofElementID eid, String str) {
        switch (eid) {
        case BRANCH -> {
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
        case RULE -> { // rule (taclet)
            {
                final AppNodeIntermediate newNode = new AppNodeIntermediate();
                currNode.addChild(newNode);
                currNode = newNode;
            }
            ruleInfo = new TacletInformation(str);
        }
        case FORMULA -> { // formula
            final int formula = Integer.parseInt(str);
            if (insideBuiltinIfInsts()) {
                // ((BuiltinRuleInformation) ruleInfo).currIfInstFormula = formula;
            } else {
                ruleInfo.currFormula = formula;
            }
        }
        case TERM -> { // term
            final PosInTerm pos = PosInTerm.parseReverseString(str);
            if (insideBuiltinIfInsts()) {
                // ((BuiltinRuleInformation) ruleInfo).currIfInstPosInTerm = pos;
            } else {
                ruleInfo.currPosInTerm = pos;
            }
        }
        case INSTANTIATION -> // inst
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            if (tacletInfo.loadedInsts == null) {
                tacletInfo.loadedInsts = new LinkedList<>();
            }
            tacletInfo.loadedInsts.add(str);
        }
        case RULESET -> {
        } // heuristics
        case ASSUMES_FORMULA_IN_SEQUENT -> // ifseqformula
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            tacletInfo.ifSeqFormulaList = tacletInfo.ifSeqFormulaList.append(str);
        }
        case ASSUMES_FORMULA_DIRECT -> // ifdirectformula
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            tacletInfo.ifDirectFormulaList = tacletInfo.ifDirectFormulaList.append(str);
        }
        case KeY_USER -> { // UserLog
            // if (proof.userLog == null) {
            // proof.userLog = new ArrayList<>();
            // }
            // proof.userLog.add(str);
        }
        case KeY_VERSION -> { // Version log
            // if (proof.keyVersionLog == null) {
            // proof.keyVersionLog = new ArrayList<>();
            // }
            // proof.keyVersionLog.add(str);
        }
        case KeY_SETTINGS -> // ProofSettings
            loadPreferences(str);
        case BUILT_IN_RULE -> { // BuiltIn rules
            {
                final AppNodeIntermediate newNode = new AppNodeIntermediate();
                currNode.addChild(newNode);
                currNode = newNode;
            }
            ruleInfo = new BuiltinRuleInformation(str);
        }
        case CONTRACT -> ((BuiltinRuleInformation) ruleInfo).currContract = str;
        case MODALITY ->
            // (additional information which can be used in external tools such as proof management)
            ((BuiltinRuleInformation) ruleInfo).currContractModality = str;
        // case ASSUMES_INST_BUILT_IN -> { // ifInst (for built in rules)
        // BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;
        // if (builtinInfo.builtinIfInsts == null) {
        // builtinInfo.builtinIfInsts = ImmutableSLList.nil();
        // }
        // builtinInfo.currIfInstFormula = 0;
        // builtinInfo.currIfInstPosInTerm = PosInTerm.getTopLevel();
        // }
        case NEW_NAMES -> {
            final String[] newNames = str.split(",");
            ruleInfo.currNewNames = ImmutableSLList.nil();
            for (String newName : newNames) {
                ruleInfo.currNewNames = ruleInfo.currNewNames.append(new Name(newName));
            }
        }
        // case AUTOMODE_TIME -> {
        // try {
        // proof.addAutoModeTime(Long.parseLong(str));
        // } catch (NumberFormatException ignore) {
        // }
        // }
        // case MERGE_PROCEDURE -> // merge procedure
        // ((BuiltinRuleInformation) ruleInfo).currMergeProc = str;
        // case NUMBER_MERGE_PARTNERS -> // number of merge partners
        // ((BuiltinRuleInformation) ruleInfo).currNrPartners = Integer.parseInt(str);
        // case MERGE_NODE -> // corresponding merge node id
        // ((BuiltinRuleInformation) ruleInfo).currCorrespondingMergeNodeId =
        // Integer.parseInt(str);
        // case MERGE_ID -> // merge node id
        // ((BuiltinRuleInformation) ruleInfo).currMergeNodeId = Integer.parseInt(str);
        // case MERGE_DIST_FORMULA -> // distinguishing formula for merges
        // ((BuiltinRuleInformation) ruleInfo).currDistFormula = str;
        // case MERGE_PREDICATE_ABSTRACTION_LATTICE_TYPE -> { // type of predicate
        // // abstraction lattice
        // try {
        // ((BuiltinRuleInformation) ruleInfo).currPredAbstraLatticeType =
        // (Class<? extends AbstractPredicateAbstractionLattice>) Class.forName(str);
        // } catch (ClassNotFoundException e) {
        // errors.add(e);
        // }
        // }
        // case MERGE_ABSTRACTION_PREDICATES -> ((BuiltinRuleInformation)
        // ruleInfo).currAbstractionPredicates =
        // str;
        // case MERGE_USER_CHOICES -> ((BuiltinRuleInformation) ruleInfo).currUserChoices = str;
        case NOTES -> {
            ruleInfo.notes = str;
            if (currNode != null) {
                ((AppNodeIntermediate) currNode).setNotes(ruleInfo.notes);
            }
        }
        // case SOLVERTYPE -> ((BuiltinRuleInformation) ruleInfo).solver = str;
        default -> {
        }
        }
    }

    @Override
    public void endExpr(ProofElementID eid, int lineNr) {
        switch (eid) {
        case BRANCH -> currNode = stack.pop();
        case USER_INTERACTION -> {
            if (currNode != null) {
                ((AppNodeIntermediate) currNode).setInteractiveRuleApplication(true);
            }
        }
        case PROOF_SCRIPT -> {
            if (currNode != null) {
                ((AppNodeIntermediate) currNode).setScriptRuleApplication(true);
            }
        }
        case RULE -> { // rule (taclet)
            ((AppNodeIntermediate) currNode).setIntermediateRuleApp(constructTacletApp());
            ((AppNodeIntermediate) currNode).getIntermediateRuleApp().setLineNr(lineNr);
        }
        case BUILT_IN_RULE -> { // BuiltIn rules
            ((AppNodeIntermediate) currNode).setIntermediateRuleApp(constructBuiltInApp());
            ((AppNodeIntermediate) currNode).getIntermediateRuleApp().setLineNr(lineNr);
        }
        // case ASSUMES_INST_BUILT_IN -> { // ifInst (for built in rules)
        // BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;
        // builtinInfo.builtinIfInsts =
        // builtinInfo.builtinIfInsts.append(new Pair<>(
        // builtinInfo.currIfInstFormula, builtinInfo.currIfInstPosInTerm));
        // }
        default -> {
        }
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
        return new BuiltInAppIntermediate(builtinInfo.currRuleName,
            new Pair<>(builtinInfo.currFormula, builtinInfo.currPosInTerm),
            builtinInfo.currContract, builtinInfo.currContractModality,
            builtinInfo.builtinIfInsts, builtinInfo.currNewNames);
    }

    /**
     * Loads proof settings.
     *
     * @param preferences The preferences to load.
     */
    private void loadPreferences(String preferences) {
        // final ProofSettings proofSettings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
        // proofSettings.loadSettingsFromPropertyString(preferences);
    }

    /**
     * @return True iff we are currently parsing a built-in rule and are inside an if-insts sub
     *         expression.
     */
    private boolean insideBuiltinIfInsts() {
        // return ruleInfo.isBuiltinInfo()
        // && ((BuiltinRuleInformation) ruleInfo).builtinIfInsts != null;
        return false;
    }

    /**
     * General information about taclet and built-in rule applications.
     *
     * @author Dominic Scheurer
     */
    private static abstract class RuleInformation {
        /* + General Information */
        protected String currRuleName;
        protected int currFormula = 0;
        protected PosInTerm currPosInTerm = PosInTerm.getTopLevel();
        protected ImmutableList<Name> currNewNames = null;
        protected String notes = null;

        protected RuleInformation(String ruleName) {
            this.currRuleName = ruleName.trim();
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

        public BuiltinRuleInformation(String ruleName) {
            super(ruleName);
        }
    }

    /**
     * Simple structure comprising the results of the parser.
     *
     * @author Dominic Scheurer
     */
    public record Result(List<Throwable> errors, String status,
            BranchNodeIntermediate parsedResult) {
    }
}
