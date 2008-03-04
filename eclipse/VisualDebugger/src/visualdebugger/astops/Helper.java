package visualdebugger.astops;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.Statement;

/**
 * Utitility class.
 *
 */
public class Helper {
	/**
	 * Hidden. Call the static methods.
	 */
	private Helper() {
	}

	/**
	 * Finds the parent {@link Block} of a {@link Statement}.
	 *
	 * @param s
	 *            the {@link Statement} to find the its parent {@link Block} for
	 * @return the parent block of {@code s}
	 */
	public static Block getParentBlock(Statement s) {
		ASTNode node = s;
		while (!(node instanceof Block)) {
			node = node.getParent();
		}
		return (Block) node;
	}
}
