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
 * TODO: Document.
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
     * TODO: Document.
     *
     * @param proof
     */
    public IntermediatePresentationProofFileParser(Proof proof) {
        this.proof = proof;
        this.currNode = this.root;
    }

    @Override
    public void beginExpr(char eid, String str) {
        switch (eid) {
        case 'b': // branch
        {
            final BranchNodeIntermediate newNode = new BranchNodeIntermediate(
                    str);
            
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

        case 'r': // rule (taclet)
        {
            final AppNodeIntermediate newNode = new AppNodeIntermediate();
            currNode.addChild(newNode);
            currNode = newNode;
        }
            
            ruleInfo = new TacletInformation(str);
            break;

        case 'f': // formula
            final int formula = Integer.parseInt(str);
            if (insideBuiltinIfInsts()) {
                ((BuiltinRuleInformation) ruleInfo).currIfInstFormula = formula;
            }
            else {
                ruleInfo.currFormula = formula;
            }
            break;

        case 't': // term
            final PosInTerm pos = PosInTerm.parseReverseString(str);
            if (insideBuiltinIfInsts()) {
                ((BuiltinRuleInformation) ruleInfo).currIfInstPosInTerm = pos;
            }
            else {
                ruleInfo.currPosInTerm = pos;
            }
            break;

        case 'i': // inst
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            if (tacletInfo.loadedInsts == null) {
                tacletInfo.loadedInsts = new LinkedList<String>();
            }
            tacletInfo.loadedInsts.add(str);
        }
            break;

        case 'h': // heuristics
            break;

        case 'q': // ifseqformula
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            tacletInfo.ifSeqFormulaList = tacletInfo.ifSeqFormulaList.append(str);
        }
            break;

        case 'd': // ifdirectformula
        {
            TacletInformation tacletInfo = (TacletInformation) ruleInfo;
            tacletInfo.ifDirectFormulaList = tacletInfo.ifDirectFormulaList.append(str);
        }
            break;

        case 'u': // UserLog
            if (proof.userLog == null) {
                proof.userLog = new Vector<String>();
            }
            proof.userLog.add(str);
            break;

        case 'v': // Version log
            if (proof.keyVersionLog == null) {
                proof.keyVersionLog = new Vector<String>();
            }
            proof.keyVersionLog.add(str);
            break;

        case 's': // ProofSettings
            loadPreferences(str);
            break;

        case 'n': // BuiltIn rules
        {
            final AppNodeIntermediate newNode = new AppNodeIntermediate();
            currNode.addChild(newNode);
            currNode = newNode;
        }
        
            ruleInfo = new BuiltinRuleInformation(str);
            break;

        case 'c': // contract
            ((BuiltinRuleInformation) ruleInfo).currContract = str;
            break;

        case 'x': // ifInst (for built in rules)
            BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;
            
            if (builtinInfo.builtinIfInsts == null) {
                builtinInfo.builtinIfInsts = ImmutableSLList
                        .<Pair<Integer, PosInTerm>> nil();
            }
            builtinInfo.currIfInstFormula = 0;
            builtinInfo.currIfInstPosInTerm = PosInTerm.getTopLevel();
            break;

        case 'w': // newnames
            final String[] newNames = str.split(",");
            ruleInfo.currNewNames = ImmutableSLList.<Name> nil();
            for (int in = 0; in < newNames.length; in++) {
                ruleInfo.currNewNames = ruleInfo.currNewNames.append(new Name(newNames[in]));
            }
            break;

        case 'e': // autoModeTime
            try {
                proof.addAutoModeTime(Long.parseLong(str));
            }
            catch (NumberFormatException e) {
                /* ignore */
            }
            break;

        case 'o': // join procedure
            ((BuiltinRuleInformation) ruleInfo).currJoinProc = str;
            break;

        case 'p': // number of join partners
            ((BuiltinRuleInformation) ruleInfo).currNrPartners = Integer.parseInt(str);
            break;

        case 'j': // corresponding join node id
            ((BuiltinRuleInformation) ruleInfo).currCorrespondingJoinNodeId = Integer.parseInt(str);
            break;

        case 'I': // join node id
            ((BuiltinRuleInformation) ruleInfo).currJoinNodeId = Integer.parseInt(str);
            break;
        }

    }

    @Override
    public void endExpr(char eid, int stringLiteralLine) {
        switch (eid) {
        case 'b': // branch
            currNode = stack.pop();
            break;

        case 'a': // userinteraction
            if (currNode != null) {
                ((AppNodeIntermediate) currNode)
                        .setInteractiveRuleApplication(true);
            }
            break;

        case 'r': // rule (taclet)
            ((AppNodeIntermediate) currNode)
                    .setIntermediateRuleApp(constructTacletApp());
            break;

        case 'n': // BuiltIn rules
            ((AppNodeIntermediate) currNode)
                    .setIntermediateRuleApp(constructBuiltInApp());
            break;

        case 'x': // ifInst (for built in rules)
            BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;
            builtinInfo.builtinIfInsts = builtinInfo.builtinIfInsts
                    .append(new Pair<Integer, PosInTerm>(builtinInfo.currIfInstFormula,
                            builtinInfo.currIfInstPosInTerm));
            break;
        }
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
     * TODO: Document.
     *
     * @return
     */
    public BranchNodeIntermediate getParsedResult() {
       return root; 
    }

    /**
     * TODO: Document.
     *
     * @return
     */
    private TacletAppIntermediate constructTacletApp() {
        TacletInformation tacletInfo = (TacletInformation) ruleInfo;
        return new TacletAppIntermediate(tacletInfo.currRuleName,
                new Pair<Integer, PosInTerm>(tacletInfo.currFormula, tacletInfo.currPosInTerm),
                tacletInfo.loadedInsts,
                tacletInfo.ifSeqFormulaList, tacletInfo.ifDirectFormulaList, tacletInfo.currNewNames);
    }

    /**
     * TODO: Document.
     *
     * @return
     */
    private BuiltInAppIntermediate constructBuiltInApp() {
        BuiltinRuleInformation builtinInfo = (BuiltinRuleInformation) ruleInfo;
        BuiltInAppIntermediate result = null;

        if (builtinInfo.currRuleName.equals("JoinRule")) {
            result = new JoinAppIntermediate(builtinInfo.currRuleName,
                    new Pair<Integer, PosInTerm>(builtinInfo.currFormula, builtinInfo.currPosInTerm),
                    builtinInfo.currContract, builtinInfo.builtinIfInsts, builtinInfo.currJoinNodeId,
                    builtinInfo.currJoinProc, builtinInfo.currNrPartners, builtinInfo.currNewNames);
        }
        else if (builtinInfo.currRuleName.equals("CloseAfterJoin")) {
            result = new JoinPartnerAppIntermediate(builtinInfo.currRuleName,
                    new Pair<Integer, PosInTerm>(builtinInfo.currFormula, builtinInfo.currPosInTerm),
                    builtinInfo.currContract, builtinInfo.builtinIfInsts, builtinInfo.currCorrespondingJoinNodeId, builtinInfo.currNewNames);
        }
        else {
            result = new BuiltInAppIntermediate(builtinInfo.currRuleName,
                    new Pair<Integer, PosInTerm>(builtinInfo.currFormula, builtinInfo.currPosInTerm),
                    builtinInfo.currContract, builtinInfo.builtinIfInsts, builtinInfo.currNewNames);
        }

        return result;
    }
    
    /**
     * TODO: Document.
     *
     * @param preferences
     */
    private void loadPreferences(String preferences) {
        final ProofSettings proofSettings = ProofSettings.DEFAULT_SETTINGS;
        proofSettings.loadSettingsFromString(preferences);
    }
    
    /**
     * TODO: Document.
     *
     * @return
     */
    private boolean insideBuiltinIfInsts() {
        return ruleInfo.isBuiltinInfo() &&  ((BuiltinRuleInformation) ruleInfo).builtinIfInsts != null;
    }
    
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
    
    private static class BuiltinRuleInformation extends RuleInformation {
        /* + Built-In Formula Information */
        protected ImmutableList<Pair<Integer, PosInTerm>> builtinIfInsts;
        protected int currIfInstFormula;
        protected PosInTerm currIfInstPosInTerm;
        /*   > Method Contract */
        protected String currContract = null;
        /*   > Join Rule */
        protected String currJoinProc = null;
        protected int currNrPartners = 0;
        protected int currCorrespondingJoinNodeId = 0;
        protected int currJoinNodeId = 0;
        
        public BuiltinRuleInformation(String ruleName) {
            super(ruleName);
        }
    }

}
