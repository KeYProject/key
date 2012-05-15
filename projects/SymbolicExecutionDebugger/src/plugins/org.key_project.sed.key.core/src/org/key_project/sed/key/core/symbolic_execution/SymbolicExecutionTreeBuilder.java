package org.key_project.sed.key.core.symbolic_execution;

import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.NodePreorderIterator;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionLoopCondition;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionMethodCall;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionNode;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionStartNode;
import org.key_project.sed.key.core.symbolic_execution.model.impl.AbstractExecutionNode;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionBranchCondition;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionBranchNode;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionLoopCondition;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionLoopNode;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionMethodCall;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionMethodReturn;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionStartNode;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionStatement;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionTermination;
import org.key_project.sed.key.core.symbolic_execution.po.SymbolicExecutionFunctionalOperationContractPO;
import org.key_project.sed.key.core.symbolic_execution.strategy.SymbolicExecutionStrategy;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.EqualsHashCodeResetter;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.collection.DefaultEntry;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;

/**
 * <p>
 * Instances of this class are used to extract the symbolic execution tree
 * from a normal KeY's proof tree. The requirement is that the proof contains
 * a predicate which is not evaluable to filter invalid execution tree paths.
 * The easiest way to achieve this is to use a 
 * {@link SymbolicExecutionFunctionalOperationContractPO} instance as proof
 * obligation to instantiate a {@link Proof} from.
 * </p>
 * <p>
 * A symbolic execution tree consists of {@link IExecutionNode}s which 
 * represents the executed statements and other Java constructs. The root
 * of a symbolic execution tree is an {@link IExecutionStartNode} which is
 * available via {@link #getProof()}.
 * </p>
 * <p>
 * Some assumptions about how {@link Sequent}s in the proof tree looks like
 * are required to extract the symbolic execution tree. To make sure that
 * they hold (otherwise exceptions are thrown) it is required to execute
 * the {@link SymbolicExecutionStrategy} in KeY's auto mode and not to apply rules
 * manually or to use other strategies. 
 * </p>
 * <p>
 * The symbolic execution tree is not updated automatically when KeY's
 * proof tree has changed. The update must be started manually via
 * {@link #analyse()}. In this case the proof tree will be analyzed and the
 * execution tree model created or updated if it already exist. 
 * </p>
 * <p>
 * Proof trees and also symbolic execution trees are very large even in
 * small programs. For this reason it is not possible to iterate over the
 * tree via recursive method calls. Instead, an instance of
 * {@link ExecutionNodePreorderIterator} should be used to iterate over
 * a symbolic execution tree.
 * </p>
 * <p>
 * The following snippet shows the basic usage of this class to extract
 * an symbolic execution tree:
 * <pre>
 * {@code
 * Proof proof; // Create proof with proof obligation SymbolicExecutionFunctionalOperationContractPO
 * // Start KeY's auto mode with SymbolicExecutionStrategy to do the proof
 * SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(proof);
 * builder.analyse(); // Create initial symbolic execution tree
 * // Iterate over symbolic execution tree and print it into the console
 * ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(builder.getStartNode);
 * while (iter.hasNext() {
 *    IExecutionNode next = iter.next();
 *    System.out.println(next.getName());
 * }
 * // Continue proof by starting KeY's auto mode again with SymbolicExecutionStrategy
 * builder.analyse(); // Create initial symbolic execution tree
 * // Iterate again over the symbolic execution tree
 * iter = new ExecutionNodePreorderIterator(builder.getStartNode);
 * // ...
 * </pre>
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionFunctionalOperationContractPO
 * @see IExecutionNode
 * @see IExecutionStartNode
 * @see SymbolicExecutionStrategy
 * @see ExecutionNodePreorderIterator
 */
public class SymbolicExecutionTreeBuilder {
   /**
    * The {@link Proof} from which the symbolic execution tree is extracted.
    */
   private Proof proof;
   
   /**
    * The start node of the symbolic execution tree.
    */
   private ExecutionStartNode startNode;
   
   /**
    * Maps a {@link Node} of KeY's proof tree to his execution tree model representation
    * if it is available.
    */
   private Map<Node, AbstractExecutionNode> keyNodeMapping = new HashMap<Node, AbstractExecutionNode>();
   
   /**
    * Maps a loop condition of a {@link Node} of KeY's proof tree to his 
    * execution tree model representation ({@link IExecutionLoopCondition}) if it is available.
    */
   private Map<Node, ExecutionLoopCondition> keyNodeLoopConditionMapping = new HashMap<Node, ExecutionLoopCondition>();
   
   /**
    * <p>
    * Maps the loop expression to the initial loop statement which contains
    * the source code location. The repeated loop statements in KeY's proof
    * tree have no source locations.
    * </p>
    * <p>
    * The trick is that the repeated loop have exactly the same object
    * as loop expression. This means reference equality. But {@link Object#equals(Object)}
    * and {@link Object#hashCode()} is overwritten in {@link Expression}s. Which
    * leads to wrongly found loops if the expression is equal. For this reason
    * is an {@link EqualsHashCodeResetter} used.
    * </p>
    */
   private Map<EqualsHashCodeResetter<Expression>, LoopStatement> loopExpressionToLoopStatementMapping = new HashMap<EqualsHashCodeResetter<Expression>, LoopStatement>();
   
   /**
    * Represents the method call stack of the current branch in KeY's proof tree.
    */
   private LinkedList<Node> methodCallStack = new LinkedList<Node>();
   
   /**
    * Contains the exception variable which is used to check if the executed program in proof terminates normally.
    */
   private IProgramVariable exceptionVariable;

   /**
    * Constructor.
    * @param proof The {@link Proof} to extract the symbolic execution tree from.
    */
   public SymbolicExecutionTreeBuilder(Proof proof) {
      super();
      assert proof != null;
      this.proof = proof;
      this.exceptionVariable = extractExceptionVariable(proof);
      this.startNode = new ExecutionStartNode(proof.root());
      this.keyNodeMapping.put(proof.root(), this.startNode);
   }
   
   /**
    * Extracts the exception variable which is used to check if the executed program in proof terminates normally.
    * @param proof The {@link Proof} to extract variable from.
    * @return The extract variable.
    */
   protected IProgramVariable extractExceptionVariable(Proof proof) {
      Node root = proof.root();
      if (root.sequent().succedent().size() == 1) {
         Term succedent = root.sequent().succedent().getFirst().formula(); // Succedent term
         if (succedent.subs().size() == 2) {
            Term updateApplication = succedent.subs().get(1);
            if (updateApplication.subs().size() == 2) {
               JavaProgramElement updateContent = updateApplication.subs().get(1).javaBlock().program();
               if (updateContent instanceof StatementBlock) { // try catch inclusive
                  ImmutableArray<? extends Statement> updateContentBody = ((StatementBlock)updateContent).getBody();
                  if (updateContentBody.size() == 2 && updateContentBody.get(1) instanceof Try) {
                     Try tryStatement = (Try)updateContentBody.get(1);
                     if (tryStatement.getBranchCount() == 1 && tryStatement.getBranchList().get(0) instanceof Catch) {
                        Catch catchStatement = (Catch)tryStatement.getBranchList().get(0);
                        if (catchStatement.getBody() instanceof StatementBlock) {
                           StatementBlock  catchBlock = (StatementBlock)catchStatement.getBody();
                           if (catchBlock.getBody().size() == 1 && catchBlock.getBody().get(0) instanceof Assignment) {
                              Assignment assignment = (Assignment)catchBlock.getBody().get(0);
                              if (assignment.getFirstElement() instanceof IProgramVariable) {
                                 IProgramVariable var = (IProgramVariable)assignment.getFirstElement();
                                 return var;
                              }
                           }
                        }
                     }
                  }
               }
            }
         }
      }
      throw new IllegalStateException("Can't extract exception variable from proof.");
   }
   
   /**
    * Frees all resources. If this method is called it is no longer possible
    * to use the {@link SymbolicExecutionTreeBuilder} instance! Later usage
    * is not checked and punished with exceptions.
    */
   public void dispose() {
      if (keyNodeMapping != null) {
         keyNodeMapping.clear();
         keyNodeMapping = null;
      }
      if (keyNodeLoopConditionMapping != null) {
         keyNodeLoopConditionMapping.clear();
         keyNodeLoopConditionMapping = null;
      }
      if (loopExpressionToLoopStatementMapping != null) {
         loopExpressionToLoopStatementMapping.clear();
         loopExpressionToLoopStatementMapping = null;
      }
      if (methodCallStack!= null) {
         methodCallStack.clear();
         methodCallStack = null;
      }
      exceptionVariable = null;
      proof = null;
      startNode = null;
   }
   
   /**
    * Returns the {@link Proof} from which the symbolic execution tree is extracted.
    * @return The {@link Proof} from which the symbolic execution tree is extracted.
    */
   public Proof getProof() {
      return proof;
   }

   /**
    * Returns the start node of the symbolic execution tree.
    * @return The start node of the symbolic execution tree.
    */
   public IExecutionStartNode getStartNode() {
      return startNode;
   }

   /**
    * This method must be called programmatically to update the
    * symbolic execution tree. The first call will create the initial tree
    * and further call will update the existing tree.
    */
   public void analyse() {
      AnalyzerProofVisitor visitor = new AnalyzerProofVisitor();
      NodePreorderIterator iter = new NodePreorderIterator(proof.root());
      while (iter.hasNext()) {
         visitor.visit(proof, iter.next()); // This visitor pattern must be used because a recursive iteration causes StackOverflowErrors if the proof tree in KeY is to deep (e.g. simple list with 2000 elements during computation of fibonacci(7)
      }
      visitor.completeTree();
   }
   
   /**
    * This {@link ProofVisitor} is used to transfer the proof tree in KeY
    * into {@link IExecutionNode}s which forms the symbolic execution tree.
    * @author Martin Hentschel
    */
   private class AnalyzerProofVisitor implements ProofVisitor {
      /**
       * Maps the {@link Node} in KeY's proof tree to the {@link IExecutionNode} of the symbolic execution tree where the {@link Node}s children should be added to.
       */
      private Map<Node, AbstractExecutionNode> addToMapping = new HashMap<Node, AbstractExecutionNode>();

      /**
       * Maps the {@link Node} with branch conditions in KeY's proof tree to the {@link IExecutionNode} of the symbolic execution tree where the {@link Node}s children should be added to.
       */
      private Map<Node, AbstractExecutionNode> branchConditionAddToMapping = new HashMap<Node, AbstractExecutionNode>();
      
      /**
       * Branch conditions ({@link ExecutionBranchCondition}) are only applied to the 
       * execution tree model if they have at least one child. For this reason they are
       * added to the model in {@link #completeTree()} after the whole proof
       * tree of KeY was analyzed via {@link #visit(Proof, Node)}. The adding
       * of {@link ExecutionBranchCondition} to the model must be done from leaf nodes
       * to the root, but in correct child order. This {@link Deque} forms
       * the order in that the {@link ExecutionBranchCondition} must be applied.
       * The contained {@link List} makes sure that the children are applied
       * in the same order as they occur in KeY's proof tree.
       */
      private Deque<Entry<AbstractExecutionNode, List<ExecutionBranchCondition>>> branchConditionsStack = new LinkedList<Entry<AbstractExecutionNode, List<ExecutionBranchCondition>>>();

      /**
       * This utility {@link Map} helps to find a {@link List} in {@link #branchConditionsStack}
       * for the given parent node to that elements in the {@link List} should be added.
       */
      private Map<AbstractExecutionNode, List<ExecutionBranchCondition>> parentToBranchConditionMapping = new HashMap<AbstractExecutionNode, List<ExecutionBranchCondition>>();
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(Proof proof, Node visitedNode) {
         try {
            // Find the parent node (IExecutionNode) to that the execution tree model representation of the given KeY's proof tree node should be added.
            AbstractExecutionNode parentToAddTo = branchConditionAddToMapping.get(visitedNode);
            if (parentToAddTo == null) {
               Node parent = visitedNode.parent(); 
               if (parent != null) {
                  parentToAddTo = addToMapping.get(parent);
               }
               else {
                  parentToAddTo = startNode;
               }
            }
            // Transform the current proof node into a symbolic execution tree node if possible
            parentToAddTo = analyzeNode(visitedNode, parentToAddTo);
            addToMapping.put(visitedNode, parentToAddTo);
            // Check if the current node has branch conditions which should be added to the execution tree model
            if (!(parentToAddTo instanceof IExecutionStartNode) && // Ignore branch conditions before starting with code execution
                hasBranchCondition(visitedNode)) {
               NodeIterator iter = visitedNode.childrenIterator();
               while (iter.hasNext()) {
                  Node childNode = iter.next();
                  if (!visitedNode.isClosed()) { // Filter out branches that are closed
                     // Create branch condition
                     ExecutionBranchCondition condition = new ExecutionBranchCondition(childNode);
                     // Add branch condition to the branch condition attributes for later adding to the proof tree. This is required for instance to filter out branches after the symbolic execution has finished.
                     List<ExecutionBranchCondition> list = parentToBranchConditionMapping.get(parentToAddTo);
                     if (list == null) {
                        list = new LinkedList<ExecutionBranchCondition>();
                        branchConditionsStack.addFirst(new DefaultEntry<AbstractExecutionNode, List<ExecutionBranchCondition>>(parentToAddTo, list));
                        parentToBranchConditionMapping.put(parentToAddTo, list);
                     }
                     list.add(condition);
                     branchConditionAddToMapping.put(childNode, condition);
                  }
               }
            }
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
         }
      }
      
      /**
       * <p>
       * Completes the execution tree model after all {@link Node}s were visited
       * in {@link #visit(Proof, Node)}. The task of this method is to add
       * {@link ExecutionBranchCondition} to the model if they have at least one child.
       * </p>
       * <p>
       * Fore more details have a look at the documentation of {@link #branchConditionsStack}.
       * </p>
       */
      public void completeTree() {
          for (Entry<AbstractExecutionNode, List<ExecutionBranchCondition>> entry : branchConditionsStack) {
             for (ExecutionBranchCondition condition : entry.getValue()) {
                if (!ArrayUtil.isEmpty(condition.getChildren())) {
                   addChild(entry.getKey(), condition);
                }
             }
         }
      }
   }
   
   /**
    * <p>
    * Analyzes the given {@link Proof} and his contained proof tree by
    * filling the start node {@link SymbolicExecutionTreeBuilder#getStartNode()}
    * with {@link IExecutionNode}s which are instantiated if a {@link Node}
    * in KeY's proof tree applies a rule of symbolic execution.
    * </p>
    * <p>
    * <b>Attention :</b> A correct pruning requires at the moment that
    * the Taclet Option "runtimeExceptions" is set to "runtimeExceptions:allow".
    * Alternatively it is required to modify rule {@code assignment_to_reference_array_component}
    * in file {@code javaRules.key} by uncommenting {@code \add (!(#v=null) & lt(#se, length(#v)) & geq(#se,0) & arrayStoreValid(#v, #se0)==>)}. 
    * </p>
    * @param node The {@link Node} to analyze.
    * @param parentToAddTo The parent {@link IExecutionNode} to add the created execution tree model representation ({@link IExecutionNode}) of the given {@link Node} to.
    * @return The {@link IExecutionNode} to which children of the current {@link Node} should be added. If no execution tree model representation was created the return value is identical to the given one (parentToAddTo).
    */
   protected AbstractExecutionNode analyzeNode(Node node, AbstractExecutionNode parentToAddTo) {
      // Analyze node
      if (!node.isClosed()) { // Prune closed branches because they are invalid
         // Get required information
         NodeInfo info = node.getNodeInfo();
         SourceElement statement = info.getActiveStatement();
         // Update call stack
         updateCallStack(node, info, statement);
         // Check if the node is already contained in the symbolic execution tree
         AbstractExecutionNode executionNode = keyNodeMapping.get(node);
         if (executionNode == null) {
            // Try to create a new node
            executionNode = createExecutionTreeModelRepresentation(parentToAddTo, node, info, statement);
            // Check if a new node was created
            if (executionNode != null) {
               // Add new node to symbolic execution tree
               addChild(parentToAddTo, executionNode);
               keyNodeMapping.put(node, executionNode);
               parentToAddTo = executionNode;
            }
         }
         else {
            parentToAddTo = executionNode;
         }
         // Check if loop condition is available
         if (hasLoopCondition(node, statement)) {
            // Get the original loop statement
            LoopStatement loop = (LoopStatement)statement;
            Expression expression = loop.getGuardExpression();
            EqualsHashCodeResetter<Expression> resetter = new EqualsHashCodeResetter<Expression>(expression);
            LoopStatement originalStatement = loopExpressionToLoopStatementMapping.get(resetter);
            if (originalStatement == null) {
               loopExpressionToLoopStatementMapping.put(resetter, loop);
            }
            else {
               loop = originalStatement;
            }
            if (loop.getPositionInfo() != PositionInfo.UNDEFINED &&
                !isDoWhileLoopCondition(node, statement) && 
                !isForLoopCondition(node, statement)) { // do while and for loops exists only in the first iteration where the loop condition is not evaluated. They are transfered into while loops in later proof nodes. 
               ExecutionLoopCondition condition = keyNodeLoopConditionMapping.get(node);
               if (condition == null) {
                  condition = new ExecutionLoopCondition(node);
                  addChild(parentToAddTo, condition);
                  keyNodeLoopConditionMapping.put(node, condition);
               }
               parentToAddTo = condition;
            }
         }
      }
      return parentToAddTo;
   }
   
   /**
    * Updates the call stack ({@link #methodCallStack}) if the given {@link Node}
    * in KeY's proof tree is a method call.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The statement ({@link SourceElement}).
    */
   protected void updateCallStack(Node node, NodeInfo info, SourceElement statement) {
      if (isMethodCallNode(node, info, statement, true)) {
         // Remove outdated methods from call stack
         int currentLevel = computeStackSize(node);
         while (methodCallStack.size() > currentLevel) {
            methodCallStack.removeLast();
         }
         // Add new node to call stack.
         methodCallStack.addLast(node);
      }
   }

   /**
    * Creates a new execution tree model representation ({@link IExecutionNode}) 
    * if possible for the given {@link Node} in KeY's proof tree.
    * @param parent The parent {@link IExecutionNode}.
    * @param node The {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The actual statement ({@link SourceElement}).
    * @return The created {@link IExecutionNode} or {@code null} if the {@link Node} should be ignored in the symbolic execution tree.
    */
   protected AbstractExecutionNode createExecutionTreeModelRepresentation(AbstractExecutionNode parent,
                                                          Node node, 
                                                          NodeInfo info, 
                                                          SourceElement statement) {
      AbstractExecutionNode result = null;
      // Make sure that a statement (SourceElement) is available.
      if (statement != null) {
         // Get position information
         PositionInfo posInfo = statement.getPositionInfo();
         // Determine the node representation and create it if one is available
         if (isMethodCallNode(node, info, statement)) {
            result = new ExecutionMethodCall(node);
         }
         else if (isMethodReturnNode(node, info, statement, posInfo)) {
            // Find the Node in the proof tree of KeY for that this Node is the return
            Node callNode = findMethodCallNode(node);
            if (callNode != null) {
               // Find the call Node representation in SED, if not available ignore it.
               IExecutionNode callSEDNode = keyNodeMapping.get(callNode);
               if (callSEDNode != null) {
                  assert callSEDNode instanceof IExecutionMethodCall;
                  result = new ExecutionMethodReturn(node, (IExecutionMethodCall)callSEDNode);
               }
            }
         }
         else if (isTerminationNode(node, info, statement, posInfo)) {
            result = new ExecutionTermination(node, exceptionVariable);
         }
         else if (isBranchNode(node, info, statement, posInfo)) {
            result = new ExecutionBranchNode(node);
         }
         else if (isLoopNode(node, info, statement, posInfo)) {
            result = new ExecutionLoopNode(node);
         }
         else if (isStatementNode(node, info, statement, posInfo)) {
            result = new ExecutionStatement(node);
         }
      }
      return result;
   }

   /**
    * Checks if the given {@link Node} handles something in an implicit method.
    * @param node The {@link Node} to check.
    * @return {@code true} is in implicit method, {@code false} is not in implicit method.
    */
   protected boolean isInImplicitMethod(Node node) {
      Node callNode = findMethodCallNode(node);
      if (callNode != null) {
         NodeInfo callInfo = callNode.getNodeInfo();
         SourceElement callStatement = callInfo.getActiveStatement();
         return !isMethodCallNode(callNode, callInfo, callStatement);
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the given {@link Node} has a branch condition.
    * @param node The {@link Node} to check.
    * @return {@code true} has branch condition, {@code false} has no branch condition.
    */
   protected boolean hasBranchCondition(Node node) {
      if (node.childrenCount() >= 2) { // Check if it is a possible branch node, otherwise there is no need for complex computation to filter out not relevant branches
         int openChildrenCount = 0;
         NodeIterator childIter = node.childrenIterator();
         while (childIter.hasNext()) {
            Node child = childIter.next();
            // Make sure that the branch is not closed
            if (!child.isClosed()) {
               // Check if the current method on stack is not an implicit method
               Node nextSymbolicExecutionNode = searchLinearNextSymbolicExecutionNode(child);
               if (!isInImplicitMethod(nextSymbolicExecutionNode)) {
                  openChildrenCount ++;
               }
            }
         }
         return openChildrenCount >= 2;
      }
      else {
         return false;
      }
   }

   /**
    * Searches linear in the children of the given {@link Node} the
    * first one which has a symbolic execution statement.
    * @param node The {@link Node} to start search in.
    * @return The found {@link Node} with the symbolic statement or {@code null} if no one was found.
    */
   protected Node searchLinearNextSymbolicExecutionNode(Node node) {
      while (node != null && node.getNodeInfo().getActiveStatement() == null) {
         int childCount = node.childrenCount();
         if (childCount == 0) {
            node = null;
         }
         else if (childCount == 1) {
            node = node.child(0);
         }
         else {
            throw new IllegalStateException("Assumption that after a split a symoblic execution is done before a branch occurre does not hold.");
         }
      }
      return node;
   }

   /**
    * Checks if the given {@link Node} has a loop condition.
    * @param node The {@link Node} to check.
    * @param statement The actual statement ({@link SourceElement}).
    * @return {@code true} has loop condition, {@code false} has no loop condition.
    */
   protected boolean hasLoopCondition(Node node, SourceElement statement) {
      return statement instanceof LoopStatement && 
             !(statement instanceof EnhancedFor); // For each loops have no loop condition
   }
   
   /**
    * Checks if the given {@link SourceElement} is a do while loop.
    * @param node The {@link Node} to check.
    * @param statement The actual statement ({@link SourceElement}).
    * @return {@code true} is do while loop, {@code false} is something else.
    */
   protected boolean isDoWhileLoopCondition(Node node, SourceElement statement) {
      return statement instanceof Do;
   }
   
   /**
    * Checks if the given {@link SourceElement} is a for loop.
    * @param node The {@link Node} to check.
    * @param statement The actual statement ({@link SourceElement}).
    * @return {@code true} is for loop, {@code false} is something else.
    */
   protected boolean isForLoopCondition(Node node, SourceElement statement) {
      return statement instanceof For;
   }
   
   /**
    * Checks if the given node should be represented as termination.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as termination, {@code false} represent node as something else. 
    */
   protected boolean isTerminationNode(Node node, NodeInfo info, SourceElement statement, PositionInfo posInfo) {
      return "emptyModality".equals(KeYUtil.getRuleDisplayName(node));
   }
   
   /**
    * Checks if the given node should be represented as method return.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as method return, {@code false} represent node as something else. 
    */
   protected boolean isMethodReturnNode(Node node, NodeInfo info, SourceElement statement, PositionInfo posInfo) {
      return "methodCallEmpty".equals(KeYUtil.getRuleDisplayName(node));
   }
   
   /**
    * Finds the {@link Node} in the proof tree of KeY which has called the
    * method that is now executed or returned in the {@link Node}.
    * @param currentNode The {@link Node} for that the method call {@link Node} is needed.
    * @return The found call {@link Node} or {@code null} if no one was found.
    */
   protected Node findMethodCallNode(Node currentNode) {
      // Compute the stack frame size before the method is called
      final int returnStackSize = computeStackSize(currentNode) - 1;
      // Return the method from the call stack
      if (returnStackSize >= 0) {
         return methodCallStack.get(returnStackSize);
      }
      else {
         return null;
      }
   }

   /**
    * Compute the stack size of the given {@link Node} in the proof tree of KeY.
    * @param node The {@link Node} to compute stack size for.
    * @return The stack size.
    */
   protected int computeStackSize(Node node) {
      int result = 0;
      if (node != null && node.getAppliedRuleApp() != null) {
         PosInOccurrence posInOc = node.getAppliedRuleApp().posInOccurrence();
         if (posInOc != null && posInOc.constrainedFormula() != null) {
            Term term = posInOc.constrainedFormula().formula();
            if (term != null && term.subs().size() == 2) {
               Term sub = term.sub(1);
               if (sub != null) {
                  JavaBlock block = sub.javaBlock();
                  if (block != null) {
                     JavaProgramElement element = block.program();
                     if (element instanceof StatementBlock) {
                        StatementBlock b = (StatementBlock)block.program();
                        ImmutableArray<ProgramPrefix> prefix = b.getPrefixElements();
                        result = CollectionUtil.count(prefix, new IFilter<ProgramPrefix>() {
                           @Override
                           public boolean select(ProgramPrefix element) {
                              return element instanceof MethodFrame;
                           }
                        });
                     }
                  }
               }
            }
         }
      }
      return result;
   }
   
   /**
    * Checks if the given node should be represented as method call.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The statement ({@link SourceElement}).
    * @return {@code true} represent node as method call, {@code false} represent node as something else. 
    */
   protected boolean isMethodCallNode(Node node, NodeInfo info, SourceElement statement) {
      return isMethodCallNode(node, info, statement, false);
   }
   
   /**
    * Checks if the given node should be represented as method call.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The statement ({@link SourceElement}).
    * @param allowImpliciteMethods {@code true} implicit methods are included, {@code false} implicit methods are outfiltered.
    * @return {@code true} represent node as method call, {@code false} represent node as something else. 
    */
   protected boolean isMethodCallNode(Node node, NodeInfo info, SourceElement statement, boolean allowImpliciteMethods) {
      if (statement instanceof MethodBodyStatement) {
         if (allowImpliciteMethods) {
            return true;
         }
         else {
            MethodBodyStatement mbs = (MethodBodyStatement)statement;
            ProgramMethod pm = mbs.getProgramMethod(proof.getServices());
            return !pm.isImplicit(); // Do not include implicit methods
         }
      }
      else {
         return false;
      }
   }
   
   /**
    * Checks if the given node should be represented as branch node.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as branch node, {@code false} represent node as something else. 
    */
   protected boolean isBranchNode(Node node, NodeInfo info, SourceElement statement, PositionInfo posInfo) {
      return isStatementNode(node, info, statement, posInfo) &&
             (statement instanceof BranchStatement); 
   }
   
   /**
    * Checks if the given node should be represented as loop node.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as loop node, {@code false} represent node as something else. 
    */
   protected boolean isLoopNode(Node node, NodeInfo info, SourceElement statement, PositionInfo posInfo) {
      return isStatementNode(node, info, statement, posInfo) &&
             (statement instanceof LoopStatement); 
   }
   
   /**
    * Checks if the given node should be represented as statement.
    * @param node The current {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The statement ({@link SourceElement}).
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as statement, {@code false} represent node as something else. 
    */
   protected boolean isStatementNode(Node node, NodeInfo info, SourceElement statement, PositionInfo posInfo) {
      return posInfo != null && 
             posInfo.getEndPosition() != Position.UNDEFINED &&
             posInfo.getEndPosition().getLine() >= 0;  // Filter out statements where source code is missing.
   }
   
   /**
    * Adds the child to the parent.
    * @param parent The parent to add to.
    * @param child The child to add.
    */
   protected void addChild(AbstractExecutionNode parent, AbstractExecutionNode child) {
      child.setParent(parent);
      parent.addChild(child);
   }
}
