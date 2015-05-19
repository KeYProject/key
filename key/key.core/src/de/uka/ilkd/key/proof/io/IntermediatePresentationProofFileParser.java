package de.uka.ilkd.key.proof.io;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.Vector;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.intermediate.AppNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.BuiltInAppIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.RootNodeIntermediate;
import de.uka.ilkd.key.proof.io.intermediate.TacletAppIntermediate;
import de.uka.ilkd.key.util.Pair;

/**
 * TODO: Document.
 * 
 * TODO (IMPORTANT): Special properties for join-related rules.
 * 
 * @author Dominic Scheurer
 */
public class IntermediatePresentationProofFileParser implements
        IProofFileParser {

    private Proof proof = null;

    private LinkedList<String> loadedInsts = null;
    private ImmutableList<String> ifFormulaList = ImmutableSLList
            .<String> nil();
    private ImmutableList<Pair<Integer, PosInTerm>> builtinIfInsts;
    private int currIfInstFormula;
    private PosInTerm currIfInstPosInTerm;
    private String currTacletName = null;
    private int currFormula = 0;
    private PosInTerm currPosInTerm = PosInTerm.getTopLevel();
    private String currContract = null;
    private String[] newNames = null;

    private RootNodeIntermediate root = null;
    private NodeIntermediate currNode = null;

    private Stack<BranchNodeIntermediate> stack = new Stack<BranchNodeIntermediate>();

    /**
     * TODO: Document.
     *
     * @param proof
     */
    public IntermediatePresentationProofFileParser(Proof proof) {
        this.proof = proof;
        this.root = new RootNodeIntermediate();
        this.currNode = this.root;
    }

    @Override
    public void beginExpr(char eid, String str) {
        switch (eid) {
        case 'b': // branch
        {
            final BranchNodeIntermediate newNode = new BranchNodeIntermediate(
                    str);
            currNode.addChild(newNode);
            currNode = newNode;
        }

            stack.push((BranchNodeIntermediate) currNode);
            break;

        case 'r': // rule (taclet)
        {
            final AppNodeIntermediate newNode = new AppNodeIntermediate();
            currNode.addChild(newNode);
            currNode = newNode;
        }

            currTacletName = str;
            currFormula = 0;
            currPosInTerm = PosInTerm.getTopLevel();
            loadedInsts = null;
            ifFormulaList = ImmutableSLList.<String> nil();
            break;

        case 'f': // formula
            final int formula = Integer.parseInt(str);
            if (builtinIfInsts != null) {
                currIfInstFormula = formula;
            }
            else {
                currFormula = formula;
            }
            break;

        case 't': // term
            final PosInTerm pos = PosInTerm.parseReverseString(str);
            if (builtinIfInsts != null) {
                currIfInstPosInTerm = pos;
            }
            else {
                currPosInTerm = pos;
            }
            break;

        case 'i': // inst
            if (loadedInsts == null) {
                loadedInsts = new LinkedList<String>();
            }
            loadedInsts.add(str);
            break;

        case 'h': // heuristics
            break;

        case 'q': // ifseqformula
            ifFormulaList = ifFormulaList.append(str);
            break;

        case 'd': // ifdirectformula
            ifFormulaList = ifFormulaList.append(str);
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
            // loadPreferences(str); //TODO
            break;

        case 'n': // BuiltIn rules
        {
            final AppNodeIntermediate newNode = new AppNodeIntermediate();
            currNode.addChild(newNode);
            currNode = newNode;
        }

            currTacletName = str;
            // set default state
            currFormula = 0;
            currPosInTerm = PosInTerm.getTopLevel();
            builtinIfInsts = null;
            break;

        case 'c': // contract
            currContract = str;
            break;

        case 'x': // ifInst (for built in rules)
            if (builtinIfInsts == null) {
                builtinIfInsts = ImmutableSLList
                        .<Pair<Integer, PosInTerm>> nil();
            }
            currIfInstFormula = 0;
            currIfInstPosInTerm = PosInTerm.getTopLevel();
            break;

        case 'w': // newnames
            newNames = str.split(",");
            break;

        case 'e': // autoModeTime
            try {
                proof.addAutoModeTime(Long.parseLong(str));
            }
            catch (NumberFormatException e) {
                /* ignore */
            }
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
            // DS: Only construct an intermediate application, do not
            // actually apply it to the goal.
            // TODO: Why do we need currGoal?
            ((AppNodeIntermediate) currNode)
                    .setIntermediateRuleApp(constructTacletApp());
            break;

        case 'n': // BuiltIn rules
            ((AppNodeIntermediate) currNode)
                    .setIntermediateRuleApp(constructBuiltInApp());
            break;

        case 'x': // ifInst (for built in rules)
            builtinIfInsts = builtinIfInsts
                    .append(new Pair<Integer, PosInTerm>(currIfInstFormula,
                            currIfInstPosInTerm));
            break;
        }
    }

    @Override
    public String getStatus() {
        // TODO Auto-generated method stub
        return null;
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
    private TacletAppIntermediate constructTacletApp() {
        return new TacletAppIntermediate(currTacletName,
                new Pair<Integer, PosInTerm>(currFormula, currPosInTerm),
                loadedInsts, ifFormulaList, newNames);
    }

    /**
     * TODO: Document.
     *
     * @return
     */
    private BuiltInAppIntermediate constructBuiltInApp() {
        BuiltInAppIntermediate result = new BuiltInAppIntermediate(
                currTacletName, new Pair<Integer, PosInTerm>(currFormula,
                        currPosInTerm), currContract, builtinIfInsts, newNames);

        currContract = null;
        builtinIfInsts = null;

        return result;
    }

}
