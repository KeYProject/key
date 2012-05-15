package org.key_project.sed.key.core.symbolic_execution.model;

import org.key_project.sed.key.core.symbolic_execution.SymbolicExecutionTreeBuilder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;

/**
 * <p>
 * Provides the basic methods each node in a symbolic execution tree
 * should have and allows to access the children. A symbolic execution tree
 * always starts with an {@link IExecutionStartNode} and is created via
 * a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * <p>
 * The following concrete nodes are available
 * <ul>
 * <li>{@link IExecutionStartNode} (root node)</li>
 * <li>{@link IExecutionStatement} (single statement, e.g. {@code int x =  1 + 2;})</li>
 * <li>{@link IExecutionBranchNode} (branch node, e.g. {@code if(x >= 0)})</li>
 * <li>{@link IExecutionBranchCondition} (branch condition, e.g. {@code x < 0})</li>
 * <li>{@link IExecutionMethodCall} (method call, e.g. {@code foo()})</li>
 * <li>{@link IExecutionMethodReturn} (method return, e.g. {@code return 42})</li>
 * <li>{@link IExecutionTermination} (termination, e.g. {@code <end>} or {@code <uncaught java.lang.NullPointerException>})</li>
 * </ul>
 * </p>
 * <p>
 * Nodes which represents a statement of the code and have a state are
 * sub interfaces of sub interface {@link IExecutionStateNode}.
 * </p>
 * @author Martin Hentschel
 */
public interface IExecutionNode {
   /**
    * Prefix that is used in {@link IExecutionNode}s which represents an internal state in KeY which is not part of the source code.
    */
   public static final String INTERNAL_NODE_NAME_START = "<";

   /**
    * Suffix that is used in {@link IExecutionNode}s which represents an internal state in KeY which is not part of the source code.
    */
   public static final String INTERNAL_NODE_NAME_END = ">";
   
   /**
    * Returns the parent {@link IExecutionNode} or {@code null} if the
    * current node is the root.
    * @return The parent {@link IExecutionNode} or {@code null} on root.
    */
   public IExecutionNode getParent();
   
   /**
    * Returns the available children.
    * @return The available children.
    */
   public IExecutionNode[] getChildren();
   
   /**
    * Returns the {@link Services} used in {@link #getProof()}.
    * @return The {@link Services} used in {@link #getProof()}.
    */
   public Services getServices();
   
   /**
    * Returns the {@link Proof} from which the symbolic execution tree was extracted.
    * @return The {@link Proof} from which the symbolic execution tree was extracted.
    */
   public Proof getProof();
   
   /**
    * Returns the {@link Node} in KeY's proof tree which is represented by this execution tree node.
    * @return The {@link Node} in KeY's proof tree which is represented by this execution tree node.
    */
   public Node getProofNode();
   
   /**
    * Returns the {@link NodeInfo} of {@link #getProofNode()}.
    * @return The {@link NodeInfo} of {@link #getProofNode()}.
    */
   public NodeInfo getProofNodeInfo();
   
   /**
    * Returns a human readable name which describes this node in the symbolic execution tree.
    * @return The human readable name which describes this node in the symbolic execution tree.
    */
   public String getName();
}
