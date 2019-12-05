package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.proof.io.IProofFileParser;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Stack;

/**
 * @author Alexander Weigl
 * @version 1 (12/5/19)
 */
public class ProofReplayer {
    static HashMap<String, IProofFileParser.ProofElementID> prooflabel2tag = new LinkedHashMap<>(32);

    static {
        prooflabel2tag.put("branch", IProofFileParser.ProofElementID.BRANCH);
        prooflabel2tag.put("rule", IProofFileParser.ProofElementID.RULE);
        prooflabel2tag.put("term", IProofFileParser.ProofElementID.TERM);
        prooflabel2tag.put("formula", IProofFileParser.ProofElementID.FORMULA);
        prooflabel2tag.put("inst", IProofFileParser.ProofElementID.INSTANTIATION);
        prooflabel2tag.put("ifseqformula", IProofFileParser.ProofElementID.ASSUMES_FORMULA_IN_SEQUENT);
        prooflabel2tag.put("ifdirectformula", IProofFileParser.ProofElementID.ASSUMES_FORMULA_DIRECT);
        prooflabel2tag.put("heur", IProofFileParser.ProofElementID.RULESET);
        prooflabel2tag.put("builtin", IProofFileParser.ProofElementID.BUILT_IN_RULE);
        prooflabel2tag.put("keyLog", IProofFileParser.ProofElementID.KeY_LOG);
        prooflabel2tag.put("keyUser", IProofFileParser.ProofElementID.KeY_USER);
        prooflabel2tag.put("keyVersion", IProofFileParser.ProofElementID.KeY_VERSION);
        prooflabel2tag.put("keySettings", IProofFileParser.ProofElementID.KeY_SETTINGS);
        prooflabel2tag.put("contract", IProofFileParser.ProofElementID.CONTRACT);
        prooflabel2tag.put("ifInst", IProofFileParser.ProofElementID.ASSUMES_INST_BUILT_IN);
        prooflabel2tag.put("userinteraction", IProofFileParser.ProofElementID.USER_INTERACTION);
        prooflabel2tag.put("proofscript", IProofFileParser.ProofElementID.PROOF_SCRIPT);
        prooflabel2tag.put("newnames", IProofFileParser.ProofElementID.NEW_NAMES);
        prooflabel2tag.put("autoModeTime", IProofFileParser.ProofElementID.AUTOMODE_TIME);
        prooflabel2tag.put("mergeProc", IProofFileParser.ProofElementID.MERGE_PROCEDURE);
        prooflabel2tag.put("abstractionPredicates", IProofFileParser.ProofElementID.MERGE_ABSTRACTION_PREDICATES);
        prooflabel2tag.put("latticeType", IProofFileParser.ProofElementID.MERGE_PREDICATE_ABSTRACTION_LATTICE_TYPE);
        prooflabel2tag.put("nrMergePartners", IProofFileParser.ProofElementID.NUMBER_MERGE_PARTNERS);
        prooflabel2tag.put("distFormula", IProofFileParser.ProofElementID.MERGE_DIST_FORMULA);
        prooflabel2tag.put("mergeNode", IProofFileParser.ProofElementID.MERGE_NODE);
        prooflabel2tag.put("mergeId", IProofFileParser.ProofElementID.MERGE_ID);
        prooflabel2tag.put("userChoices", IProofFileParser.ProofElementID.MERGE_USER_CHOICES);
        prooflabel2tag.put("opengoal", IProofFileParser.ProofElementID.OPEN_GOAL);
    }


    public static void run(Token token, CharStream input, IProofFileParser prl) {
        input.seek(1 + token.getStopIndex()); // ends now on \proof|
        KeYLexer lexer = ParsingFacade.lex(input);
        CommonTokenStream stream = new CommonTokenStream(lexer);
        Stack<IProofFileParser.ProofElementID> stack = new Stack<>();
        Stack<Integer> posStack = new Stack<>();
        while (true) {
            int type = stream.LA(1);
            switch (type) {
                case KeYLexer.LPAREN:
                    stream.consume();
                    Token idToken = stream.LT(1);
                    IProofFileParser.ProofElementID cur = prooflabel2tag.get(idToken.getText());
                    stream.consume();

                    String arg = null;
                    int pos = idToken.getLine() + token.getLine();
                    if (stream.LA(1) == KeYLexer.STRING_LITERAL) {
                        arg = stream.LT(1).getText();
                        stream.consume();//throw string away
                        arg = arg.substring(1, arg.length() - 1);
                    }

                    prl.beginExpr(cur, arg);
                    System.out.format("Emit: %s %s%n", cur, arg);
                    stack.push(cur);
                    posStack.push(pos);
                    break;
                case KeYLexer.RPAREN:
                    prl.endExpr(stack.pop(), posStack.pop());
                    stream.consume();
                    break;
                case KeYLexer.EOF:
                    return;
                default:
                    stream.consume();
            }
        }
    }
}
