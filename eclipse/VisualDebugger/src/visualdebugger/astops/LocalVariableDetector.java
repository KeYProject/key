/**
 *
 */
package visualdebugger.astops;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;

/**
 * This class looks for local declarations of local variables, their assignmetns
 * and the references to them. <i>It is an example for how to extend
 * {@link ASTVisitor}.</i>
 *
 */
public class LocalVariableDetector extends ASTVisitor {
	Map<IVariableBinding, VariableBindingManager> localVariableManagers = new HashMap<IVariableBinding, VariableBindingManager>();

	/**
	 * Looks for local variable declarations. For every occurence of a local
	 * variable, a {@link VariableBindingManager} is created and stored in
	 * {@link #localVariableManagers} map.
	 *
	 * @param node
	 *            the node to visit
	 * @return static {@code false} to prevent that the simple name in the
	 *         declaration is understood by {@link #visit(SimpleName)} as
	 *         reference
	 */
	public boolean visit(VariableDeclarationStatement node) {
		for (Iterator iter = node.fragments().iterator(); iter.hasNext();) {
			VariableDeclarationFragment fragment = (VariableDeclarationFragment) iter
					.next();

			// VariableDeclarationFragment: is the plain variable declaration
			// part. Example:
			// "int x=0, y=0;" contains two VariableDeclarationFragments, "x=0"
			// and "y=0"

			IVariableBinding binding = fragment.resolveBinding();
			VariableBindingManager manager = new VariableBindingManager(
					fragment); // create the manager fro the fragment
			localVariableManagers.put(binding, manager);
			manager.variableInitialized(fragment.getInitializer());
			// first assignment is the initalizer
		}
		return false; // prevent that SimpleName is interpreted as
		// reference
	}

	/**
	 * Visits {@link Assignment} AST nodes (e.g. {@code x = 7 + 8} ). Resolves
	 * the binding of the left hand side (in the example: {@code x}). If the
	 * binding is found in the {@link #localVariableManagers} map, we have an
	 * assignment of a local variable. The variable binding manager of this
	 * local variable then has to be informed about this assignment.
	 *
	 * @param node
	 *            the node to visit
	 */
	public boolean visit(Assignment node) {
		if (node.getLeftHandSide() instanceof SimpleName) {
			IBinding binding = ((SimpleName) node.getLeftHandSide())
					.resolveBinding();
			if (localVariableManagers.containsKey(binding)) {
				// contains key -> it is an assignment ot a local variable

				VariableBindingManager manager = localVariableManagers
						.get(binding);

				manager.variableInitialized(node.getRightHandSide());
			}
		}
		// prevent that simplename is interpreted as reference
		return false;
	}

	/**
	 * Visits {@link SimpleName} AST nodes. Resolves the binding of the simple
	 * name and looks for it in the {@link #localVariableManagers} map. If the
	 * binding is found, this is a reference to a local variable. The variable
	 * binding manager of this local variable then has to be informed about that
	 * reference.
	 *
	 * @param node
	 *            the node to visit
	 */
	public boolean visit(SimpleName node) {
		IBinding binding = node.resolveBinding();
		if (localVariableManagers.containsKey(binding)) {
			VariableBindingManager manager = localVariableManagers.get(binding);
			manager.variableRefereneced(node);
		}
		return true;
	}

	/**
	 * Getter for the resulting map.
	 *
	 * @return a map with variable bindings as keys and
	 *         {@link VariableBindingManager} as values
	 */
	public Map<IVariableBinding, VariableBindingManager> getLocalVariableManagers() {
		return localVariableManagers;
	}

	/**
	 * Starts the process.
	 *
	 * @param unit
	 *            the AST root node. Bindings have to have been resolved.
	 */
	public void process(CompilationUnit unit) {
		unit.accept(this);
	}
}