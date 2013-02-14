package de.uka.ilkd.key.symbolic_execution;

import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionLoopNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionUseLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionUseOperationContract;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.DefaultEntry;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.NodePreorderIterator;

/**
 * <p>
 * Instances of this class are used to extract the symbolic execution tree
 * from a normal KeY's proof tree. The requirement is that the proof contains
 * a predicate which is not evaluable to filter invalid execution tree paths.
 * The easiest way to achieve this is to use a 
 * {@link FunctionalOperationContractPO} (addUninterpretedPredicate = {@code true}) instance as proof
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
 * Proof proof; // Create proof with proof obligation FunctionalOperationContractPO and set addUninterpretedPredicate to true
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
 * @see FunctionalOperationContractPO#isAddUninterpretedPredicate()
 * @see IExecutionNode
 * @see IExecutionStartNode
 * @see SymbolicExecutionStrategy
 * @see ExecutionNodePreorderIterator
 */
public class SymbolicExecutionTreeBuilder {
   /**
    * The used mediator during proof.
    */
   private KeYMediator mediator;
   
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
    * Maps a branch condition of a {@link Node} of KeY's proof tree to his 
    * execution tree model representation ({@link IExecutionBranchCondition}) if it is available.
    */
   private Map<Node, ExecutionBranchCondition> keyNodeBranchConditionMapping = new HashMap<Node, ExecutionBranchCondition>();
   
   /**
    * Represents the method call stack of the current branch in KeY's proof tree.
    */
   private LinkedList<Node> methodCallStack = new LinkedList<Node>();
   
   /**
    * Contains the exception variable which is used to check if the executed program in proof terminates normally.
    */
   private IProgramVariable exceptionVariable;
   
   /**
    * {@code true} merge branch conditions which means that a branch condition never contains another branch condition
    * or {@code false} allow that branch conditions contains branch conditions.
    */
   private boolean mergeBranchConditions = false;

   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proof The {@link Proof} to extract the symbolic execution tree from.
    */
   public SymbolicExecutionTreeBuilder(KeYMediator mediator, 
                                       Proof proof,
                                       boolean mergeBranchConditions) {
      assert mediator != null;
      assert proof != null;
      this.mediator = mediator;
      this.proof = proof;
      this.mergeBranchConditions = mergeBranchConditions;
      this.exceptionVariable = SymbolicExecutionUtil.extractExceptionVariable(proof);
      this.startNode = new ExecutionStartNode(mediator, proof.root());
      this.keyNodeMapping.put(proof.root(), this.startNode);
      initMethodCallStack(proof.root(), proof.getServices());
   }
   
   /**
    * <p>
    * This method initializes {@link #methodCallStack} in case that the
    * initial {@link Sequent} contains {@link MethodFrame}s in its modality.
    * </p>
    * <p>
    * This is required because if a block of statements is executed instead
    * of a method the initial {@link Sequent} contains also a {@link MethodFrame}.
    * This initial {@link MethodFrame} is required to simulate an execution
    * context which is required to access class members.
    * </p>
    * @param root The root {@link Node} with the initial {@link Sequent}.
    * @param services The {@link Services} to use.
    */
   protected void initMethodCallStack(final Node root, Services services) {
      // Find all modalities in the succedent
      final List<Term> modalityTerms = new LinkedList<Term>();
      for (SequentFormula sequentFormula : root.sequent().succedent()) {
         sequentFormula.formula().execPreOrder(new DefaultVisitor() {
            @Override
            public void visit(Term visited) {
               if (visited.op() instanceof Modality) {
                  modalityTerms.add(visited);
               }
            }
         });
      }
      // Make sure that at least one modality was found
      if (modalityTerms.size() >= 2) {
         throw new IllegalStateException("Sequent contains multiple modalities.");
      }
      // Check if modality contains method frames
      if (!modalityTerms.isEmpty()) {
         Term modalityTerm = modalityTerms.get(0);
         JavaBlock javaBlock = modalityTerm.javaBlock();
         final ProgramElement program = javaBlock.program(); 
         new JavaASTVisitor(program, services) {
            @Override
            protected void doDefaultAction(SourceElement node) {
            }
            
            @Override
            public void performActionOnMethodFrame(MethodFrame x) {
               methodCallStack.add(root);
            }

            public void run() {
               walk(program);
            }
         }.run();
      }
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
      if (keyNodeBranchConditionMapping != null) {
         keyNodeBranchConditionMapping.clear();
         keyNodeBranchConditionMapping = null;
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
    * Returns the used {@link KeYMediator} during proof.
    * @return The used {@link KeYMediator} during proof.
    */
   public KeYMediator getMediator() {
      return mediator;
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
         // Find the parent node (IExecutionNode) to that the execution tree model representation of the given KeY's proof tree node should be added.
         AbstractExecutionNode parentToAddTo = keyNodeBranchConditionMapping.get(visitedNode);
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
               if (!keyNodeBranchConditionMapping.containsKey(childNode)) {
                  if (!visitedNode.isClosed()) { // Filter out branches that are closed
                     // Create branch condition
                     ExecutionBranchCondition condition = new ExecutionBranchCondition(mediator, childNode);
                     // Add branch condition to the branch condition attributes for later adding to the proof tree. This is required for instance to filter out branches after the symbolic execution has finished.
                     List<ExecutionBranchCondition> list = parentToBranchConditionMapping.get(parentToAddTo);
                     if (list == null) {
                        list = new LinkedList<ExecutionBranchCondition>();
                        branchConditionsStack.addFirst(new DefaultEntry<AbstractExecutionNode, List<ExecutionBranchCondition>>(parentToAddTo, list));
                        parentToBranchConditionMapping.put(parentToAddTo, list);
                     }
                     list.add(condition);
                     keyNodeBranchConditionMapping.put(childNode, condition);
                     // Set call stack on new created node
                     condition.setCallStack(createCallStack(childNode, childNode.getAppliedRuleApp(), childNode.getNodeInfo().getActiveStatement()));
                  }
               }
            }
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
                AbstractExecutionNode[] conditionsChildren = condition.getChildren(); 
                if (!JavaUtil.isEmpty(conditionsChildren)) {
                   if (mergeBranchConditions) {
                      // Merge branch conditions if possible
                      boolean addingToParentRequired = false;
                      for (AbstractExecutionNode child : conditionsChildren) {
                         if (child instanceof ExecutionBranchCondition) {
                            ExecutionBranchCondition bcChild = (ExecutionBranchCondition)child;
                            bcChild.addMergedProofNode(condition.getProofNode());
                            addChild(entry.getKey(), child); // Move child one up in hierarchy
                         }
                         else {
                            addingToParentRequired = true; // Adding of current branch condition is required because non branch condition children are available
                         }
                      }
                      if (addingToParentRequired) {
                         addChild(entry.getKey(), condition);
                      }
                   }
                   else {
                      // Add all branch conditions without merging
                      addChild(entry.getKey(), condition);
                   }
                }
                else {
                   keyNodeBranchConditionMapping.remove(condition.getProofNode());
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
         updateCallStack(node, statement);
         // Check if the node is already contained in the symbolic execution tree
         AbstractExecutionNode executionNode = keyNodeMapping.get(node);
         if (executionNode == null) {
            // Try to create a new node
            executionNode = createExecutionTreeModelRepresentation(parentToAddTo, node, statement);
            // Check if a new node was created
            if (executionNode != null) {
               // Add new node to symbolic execution tree
               addChild(parentToAddTo, executionNode);
               keyNodeMapping.put(node, executionNode);
               parentToAddTo = executionNode;
               // Set call stack on new created node
               executionNode.setCallStack(createCallStack(node, node.getAppliedRuleApp(), statement));
            }
         }
         else {
            parentToAddTo = executionNode;
         }
         // Check if loop condition is available
         if (SymbolicExecutionUtil.hasLoopCondition(node, node.getAppliedRuleApp(), statement)) {
            if (((LoopStatement)statement).getGuardExpression().getPositionInfo() != PositionInfo.UNDEFINED &&
                !SymbolicExecutionUtil.isDoWhileLoopCondition(node, statement) && 
                !SymbolicExecutionUtil.isForLoopCondition(node, statement)) { // do while and for loops exists only in the first iteration where the loop condition is not evaluated. They are transfered into while loops in later proof nodes. 
               ExecutionLoopCondition condition = keyNodeLoopConditionMapping.get(node);
               if (condition == null) {
                  condition = new ExecutionLoopCondition(mediator, node);
                  addChild(parentToAddTo, condition);
                  keyNodeLoopConditionMapping.put(node, condition);
                  // Set call stack on new created node
                  condition.setCallStack(createCallStack(node, node.getAppliedRuleApp(), statement));
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
    * @param node The current {@link Node}.
    * @param statement The statement ({@link SourceElement}).
    */
   protected void updateCallStack(Node node, 
                                  SourceElement statement) {
      if (SymbolicExecutionUtil.isMethodCallNode(node, node.getAppliedRuleApp(), statement, true)) {
         // Remove outdated methods from call stack
         int currentLevel = SymbolicExecutionUtil.computeStackSize(node, node.getAppliedRuleApp());
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
    * @param statement The actual statement ({@link SourceElement}).
    * @return The created {@link IExecutionNode} or {@code null} if the {@link Node} should be ignored in the symbolic execution tree.
    */
   protected AbstractExecutionNode createExecutionTreeModelRepresentation(AbstractExecutionNode parent,
                                                                          Node node, 
                                                                          SourceElement statement) {
      AbstractExecutionNode result = null;
      // Make sure that a statement (SourceElement) is available.
      if (statement != null) {
         // Get position information
         PositionInfo posInfo = statement.getPositionInfo();
         // Determine the node representation and create it if one is available
         if (SymbolicExecutionUtil.isMethodCallNode(node, node.getAppliedRuleApp(), statement)) {
            result = new ExecutionMethodCall(mediator, node);
         }
         else if (SymbolicExecutionUtil.isMethodReturnNode(node, node.getAppliedRuleApp())) {
            // Find the Node in the proof tree of KeY for that this Node is the return
            Node callNode = findMethodCallNode(node, node.getAppliedRuleApp());
            if (callNode != null) {
               // Find the call Node representation in SED, if not available ignore it.
               IExecutionNode callSEDNode = keyNodeMapping.get(callNode);
               if (callSEDNode instanceof IExecutionMethodCall) { // Could be the start node if the initial sequent already contains some method frames.
                  result = new ExecutionMethodReturn(mediator, node, (IExecutionMethodCall)callSEDNode);
               }
            }
         }
         else if (SymbolicExecutionUtil.isTerminationNode(node, node.getAppliedRuleApp())) {
            result = new ExecutionTermination(mediator, node, exceptionVariable);
         }
         else if (SymbolicExecutionUtil.isBranchNode(node, node.getAppliedRuleApp(), statement, posInfo)) {
            result = new ExecutionBranchNode(mediator, node);
         }
         else if (SymbolicExecutionUtil.isLoopNode(node, node.getAppliedRuleApp(), statement, posInfo)) {
            if (SymbolicExecutionUtil.isFirstLoopIteration(node, node.getAppliedRuleApp(), statement)) {
               result = new ExecutionLoopNode(mediator, node);
            }
         }
         else if (SymbolicExecutionUtil.isStatementNode(node, node.getAppliedRuleApp(), statement, posInfo)) {
            result = new ExecutionStatement(mediator, node);
         }
      }
      else if (SymbolicExecutionUtil.isUseOperationContract(node, node.getAppliedRuleApp())) {
         result = new ExecutionUseOperationContract(mediator, node);
      }
      else if (SymbolicExecutionUtil.isUseLoopInvariant(node, node.getAppliedRuleApp())) {
         result = new ExecutionUseLoopInvariant(mediator, node);
      }
      return result;
   }
   
   /**
    * Computes the method call stack of the given {@link Node}.
    * @param node The {@link Node}.
    * @param ruleApp The applied {@link RuleApp} on the given {@link Node}.
    * @param statement The active statement of the given {@link Node}.
    * @return The computed method call stack.
    */
   protected IExecutionNode[] createCallStack(Node node, RuleApp ruleApp, SourceElement statement) {
      // Compute number of call stack size
      int size = SymbolicExecutionUtil.computeStackSize(node, ruleApp);
      // Add call stack entries
      List<IExecutionNode> callStack = new LinkedList<IExecutionNode>();
      Iterator<Node> stackIter = methodCallStack.iterator();
      for (int i = 0; i < size; i++) {
         Node stackEntry = stackIter.next();
         if (stackEntry != proof.root()) { // Ignore call stack entries provided by the initial sequent
            IExecutionNode executionNode = getExecutionNode(stackEntry);
            assert executionNode != null : "Can't find execution node for KeY's proof node \"" + stackEntry + "\".";
            callStack.add(executionNode);
         }
      }
      return callStack.toArray(new IExecutionNode[callStack.size()]);
   }

   /**
    * Finds the {@link Node} in the proof tree of KeY which has called the
    * method that is now executed or returned in the {@link Node}.
    * @param currentNode The {@link Node} for that the method call {@link Node} is needed.
    * @return The found call {@link Node} or {@code null} if no one was found.
    */
   protected Node findMethodCallNode(Node currentNode, RuleApp ruleApp) {
      // Compute the stack frame size before the method is called
      final int returnStackSize = SymbolicExecutionUtil.computeStackSize(currentNode, ruleApp) - 1;
      // Return the method from the call stack
      if (returnStackSize >= 0) {
         return methodCallStack.get(returnStackSize);
      }
      else {
         return null;
      }
   }

   /**
    * Checks if the given {@link Node} handles something in an implicit method.
    * @param node The {@link Node} to check.
    * @return {@code true} is in implicit method, {@code false} is not in implicit method.
    */
   protected boolean isInImplicitMethod(Node node) {
      return SymbolicExecutionUtil.isInImplicitMethod(node, node.getAppliedRuleApp());
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
               Node previousSymbolicExecutionNode = searchPreviousSymbolicExecutionNode(child);
               if (!isInImplicitMethod(previousSymbolicExecutionNode)) {
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
    * Searches the first node in the parent hierarchy (including the given node)
    * which executes a statement.
    * @param node The {@link Node} to start search in.
    * @return The found {@link Node} with the symbolic statement or {@code null} if no one was found.
    */
   protected Node searchPreviousSymbolicExecutionNode(Node node) {
      while (node != null && node.getNodeInfo().getActiveStatement() == null) {
         node = node.parent();
      }
      return node;
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

   /**
    * Searches the {@link IExecutionNode} which represents the given {@link Node} of KeY's proof tree.
    * @param proofNode The {@link Node} in KeY's proof tree.
    * @return The {@link IExecutionNode} representation or {@code null} if no one is available.
    */
   public IExecutionNode getExecutionNode(Node proofNode) {
      IExecutionNode result = keyNodeMapping.get(proofNode);
      if (result == null) {
         result = keyNodeBranchConditionMapping.get(proofNode);
      }
      if (result == null) {
         result = keyNodeLoopConditionMapping.get(proofNode);
      }
      return result;
   }
}
