import java.util.BitSet;

import com.puppycrawl.tools.checkstyle.api.AbstractCheck;
import com.puppycrawl.tools.checkstyle.api.DetailAST;
import com.puppycrawl.tools.checkstyle.api.TokenTypes;
import com.puppycrawl.tools.checkstyle.utils.TokenUtils;

import static com.puppycrawl.tools.checkstyle.api.TokenTypes.*;

/**
 * This class implements a checkstyle rule which asserts that increment and
 * decrement expressions do only occur as individual commands.
 *
 * This is meant to avoid rather unreadable code like
 *
 * <pre>
 *   for (int k = left; ++left <= right; k = ++left)
 * </pre>
 *
 * (taken from JDK's DualPivotQuicksort.java).
 *
 * <h2>Check</h2>
 *
 * The check scans all occurrences of pre- and postincrements and checks their
 * parents and grandparents in the AST. First parent is checked (see
 * "admissibleParents" in configuration below). If the parent is EXPR, then
 * the grandparent AST type is also checked.
 *
 * <h2>Configuration</h2>
 *
 * The check can be configured from the style file as follows:
 *
 * <pre>
 *   &lt;module name="NoEmbeddedPlusPlus"&gt;
 *     &lt;property name="admissibleParents" value="EXPR"/&gt;
 *     &lt;property name="admissibleGrandParents"
 *                  value="SLIST, ELIST, LITERAL_WHILE,
 *                         LITERAL_FOR, LITERAL_IF"/&gt;
 *     &lt;message key="parent"
 *                 value="Unallowed increment/decrement operation."/&gt;
 *     &lt;message key="grandParent"
 *                 value="Unallowed increment/decrement operation."/&gt;
 *   &lt;/module&gt;
 * </pre>
 *
 * This lists also the default values.
 *
 * @author Mattias Ulbrich
 * @version 1
 * @since May 2017
 */
public class NoEmbeddedPlusPlusCheck extends AbstractCheck {

    private static final int[] DEFAULT_TOKENS =
        { DEC, INC, POST_DEC, POST_INC };

    private static final int[] ADMISSIBLE_PARENTS =
        { EXPR };

    private static final int[] ADMISSIBLE_GRAND_PARENTS =
        { SLIST, ELIST, LITERAL_WHILE, LITERAL_FOR, LITERAL_IF };

    private static final String DEFAULT_PARENT_MESSAGE =
            "Unallowed increment/decrement operation.";

    private static final String DEFAULT_GRAND_PARENT_MESSAGE =
            "Unallowed increment/decrement operation.";

    private BitSet admissibleParents = new BitSet();
    private BitSet admissibleGrandParents = new BitSet();
    private String parentMessage = DEFAULT_PARENT_MESSAGE;
    private String grandParentMessage = DEFAULT_GRAND_PARENT_MESSAGE;

    public NoEmbeddedPlusPlusCheck() {
        setBits(this.admissibleParents, ADMISSIBLE_PARENTS);
        setBits(this.admissibleGrandParents, ADMISSIBLE_GRAND_PARENTS);
    }

    private void setBits(BitSet bitset, int[] bits) {
        for (int bit : bits) {
            bitset.set(bit);
        }
    }

    @Override
    public void visitToken(DetailAST ast) {

        DetailAST parent = ast.getParent();

        if(parent != null) {
            int id = parent.getType();
            if(!admissibleParents.get(id)) {
                log(ast.getLineNo(), ast.getColumnNo(),
                        parentMessage);
            }

            if(id == TokenTypes.EXPR) {
                int gid = parent.getParent().getType();
                if(!admissibleGrandParents.get(gid)) {
                    log(ast.getLineNo(), ast.getColumnNo(),
                            grandParentMessage);
                }
            }
        }

    }

    @Override
    public int[] getDefaultTokens() {
        return DEFAULT_TOKENS;
    }

    public void setAdmissibleParents(String... parentTokens) {
        admissibleParents.clear();
        for (int i = 0; i < parentTokens.length; i++) {
            admissibleParents.set(TokenUtils.getTokenId(parentTokens[i]));
        }
    }

    public void setParentMessage(String parentMessage) {
        this.parentMessage = parentMessage;
    }

    public void setGrandAdmissibleParents(String... parentTokens) {
        admissibleGrandParents.clear();
        for (int i = 0; i < parentTokens.length; i++) {
            admissibleGrandParents.set(TokenUtils.getTokenId(parentTokens[i]));
        }
    }


    public void setGrandParentMessage(String grandParentMessage) {
        this.grandParentMessage = grandParentMessage;
    }

}
