package org.key_project.sed.key.core.model;

import java.io.File;
import java.io.IOException;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.internal.ui.javaeditor.ASTProvider;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISourceNameProvider;
import org.key_project.sed.core.model.memory.ISEDMemoryDebugNode;
import org.key_project.sed.core.model.memory.ISEDMemoryStackFrameCompatibleDebugNode;
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEDMemoryBranchNode;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryLoopCondition;
import org.key_project.sed.core.model.memory.SEDMemoryLoopNode;
import org.key_project.sed.core.model.memory.SEDMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryTermination;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.key.core.strategy.DebuggerStrategy;
import org.key_project.sed.key.core.util.ASTNodeByEndIndexSearcher;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.EqualsHashCodeResetter;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.collection.DefaultEntry;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Implementation if {@link ISEDDebugTarget} which uses KeY to symbolically
 * debug a program.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYDebugTarget extends SEDMemoryDebugTarget {
   /**
    * Prefix that is used in {@link ISEDDebugNode}s which represents an internal state in KeY which is not part of the source code.
    */
   public static final String INTERNAL_NODE_START = "<";

   /**
    * Suffix that is used in {@link ISEDDebugNode}s which represents an internal state in KeY which is not part of the source code.
    */
   public static final String INTERNAL_NODE_END = ">";
   
   /**
    * The default name of the only contained {@link ISEDThread}.
    */
   public static final String DEFAULT_THREAD_NAME = "KeY Default Thread";
   
   /**
    * The default name of a termination node.
    */
   public static final String DEFAULT_TERMINATION_NODE_NAME = INTERNAL_NODE_START + "end" + INTERNAL_NODE_END;
   
   /**
    * The used model identifier.
    */
   public static final String MODEL_IDENTIFIER = "org.key_project.sed.key.core";

   /**
    * The used name if the name of a method is unknown.
    */
   public static final String UNKNOWN_METHOD_NAME = INTERNAL_NODE_START + "Unknown Method" + INTERNAL_NODE_END;
   
   /**
    * The proof in KeY to tread.
    */
   private Proof proof;
   
   /**
    * The only contained child thread.
    */
   private SEDMemoryThread thread;
   
   /**
    * Listens for changes on the auto mode of KeY Main Frame,.
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStarted(ProofEvent e) {
         handleAutoModeStarted(e);
      }

      @Override
      public void autoModeStopped(ProofEvent e) {
         handleAutoModeStopped(e);
      }
   };
   
   /**
    * Maps a {@link Node} of KeY's proof tree to his debug model representation
    * if it is available.
    */
   private Map<Node, ISEDDebugNode> keyNodeMapping;
   
   /**
    * Maps a loop condition of a {@link Node} of KeY's proof tree to his 
    * debug model representation ({@link ISEDLoopCondition}) if it is available.
    */
   private Map<Node, ISEDLoopCondition> keyNodeLoopConditionMapping;
   
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
    * leads to wrongly found loops if the expression is equal. For this reason as
    * key is an {@link EqualsHashCodeResetter} used.
    * </p>
    */
   private Map<EqualsHashCodeResetter<Expression>, LoopStatement> loopExpressionToLoopStatementMapping;
   
   /**
    * Represents the method call stack of the current branch in KeY's proof tree.
    */
   private LinkedList<Node> methodCallStack;
   
   /**
    * Constructor.
    * @param launch The parent {@link ILaunch}.
    * @param proof The {@link Proof} in KeY to treat.
    */
   public KeYDebugTarget(ILaunch launch, Proof proof) {
      super(launch);
      // Update references
      Assert.isNotNull(proof);
      this.proof = proof;
      // Update initial model
      setModelIdentifier(MODEL_IDENTIFIER);
      setName(proof.name() != null ? proof.name().toString() : "Unnamed");
      thread = new SEDMemoryThread(getDebugTarget());
      thread.setName(DEFAULT_THREAD_NAME);
      addSymbolicThread(thread);
      keyNodeMapping = new HashMap<Node, ISEDDebugNode>();
      keyNodeLoopConditionMapping = new HashMap<Node, ISEDLoopCondition>();
      loopExpressionToLoopStatementMapping = new HashMap<EqualsHashCodeResetter<Expression>, LoopStatement>();
      methodCallStack = new LinkedList<Node>();
      // Observe frozen state of KeY Main Frame
      MainWindow.getInstance().getMediator().addAutoModeListener(autoModeListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return super.canResume() && 
             !MainWindow.getInstance().frozen && // Only one proof completion per time is possible
             KeYUtil.isProofInUI(proof); // Otherwise Auto Mode is not available.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      if (canResume()) {
         // Inform UI that the process is resumed
         super.resume();
         // Set strategy to use
         StrategyProperties strategyProperties = DebuggerStrategy.getDebuggerStrategyProperties(true, false, false, true);
         proof.setActiveStrategy(new DebuggerStrategy.Factory().create(proof, strategyProperties));
         // Run proof
         KeYUtil.runProofInAutomaticModeWithoutResultDialog(proof);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return super.canSuspend() && 
             MainWindow.getInstance().frozen && // Only if the auto mode is in progress
             MainWindow.getInstance().getMediator().getProof() == proof; // And the auto mode handles this proof
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      if (canSuspend()) {
         MainWindow.getInstance().getMediator().stopAutoMode();
      }
   }

   /**
    * Analyzes the given {@link Proof} and his contained proof tree by
    * filling the contained default {@link ISEDThread} of this {@link ISEDDebugTarget}
    * with {@link ISEDDebugNode}s which are instantiated if a {@link Node}
    * in KeY's proof tree applies a rule of symbolic execution.
    * @param proof The {@link Proof} to analyze.
    * @throws DebugException Occurred Exception.
    */
   protected void analyzeProof(Proof proof) throws DebugException {
      AnalyzerProofVisitor visitor = new AnalyzerProofVisitor();
      proof.breadthFirstSearch(proof.root(), visitor); // This visitor pattern must be used because a recursive iteration causes StackOverflowErrors if the proof tree in KeY is to deep (e.g. simple list with 2000 elements during computation of fibonacci(7)
      visitor.completeTree();
   }
   
   /**
    * This {@link ProofVisitor} is used to transfer the proof tree in KeY
    * into {@link ISEDDebugNode}s which are used in the symbolic debugger.
    * @author Martin Hentschel
    */
   private class AnalyzerProofVisitor implements ProofVisitor {
      /**
       * Maps the {@link Node} in KeY's proof tree to the {@link ISEDDebugNode} of the debugger where the {@link Node}s children should be added to.
       */
      private Map<Node, ISEDDebugNode> addToMapping = new HashMap<Node, ISEDDebugNode>();

      /**
       * Branch conditions ({@link ISEDBranchCondition}) are only applied to the 
       * debug model if they have at least one child. For this reason they are
       * added to the model in {@link #completeTree()} after the whole proof
       * tree of KeY was analyzed via {@link #visit(Proof, Node)}. The adding
       * of {@link ISEDBranchCondition} to the model must be done from leaf nodes
       * to the root, but in correct child order. This {@link Deque} forms
       * the order in that the {@link ISEDBranchCondition} must be applied.
       * The contained {@link List} makes sure that the children are applied
       * in the same order as they occur in KeY's proof tree.
       */
      private Deque<Entry<ISEDDebugNode, List<ISEDBranchCondition>>> branchConditionsStack = new LinkedList<Entry<ISEDDebugNode,List<ISEDBranchCondition>>>();

      /**
       * This utility {@link Map} helps to find a {@link List} in {@link #branchConditionsStack}
       * for the given parent node to that elements in the {@link List} should be added.
       */
      private Map<ISEDDebugNode, List<ISEDBranchCondition>> parentToBranchConditionMapping = new HashMap<ISEDDebugNode, List<ISEDBranchCondition>>();
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(Proof proof, Node visitedNode) {
         try {
            // Find the parent node (ISEDDebugNode) to that the debug model representation of the given KeY's proof tree node should be added.
            ISEDDebugNode parentToAddTo;
            Node parent = visitedNode.parent(); 
            if (parent != null) {
               parentToAddTo = addToMapping.get(parent);
            }
            else {
               parentToAddTo = thread;
            }
            // Check if the current node has a branch condition which should be added to the debug model
            boolean hasMultipleBranches = parent != null && parent.childrenCount() >= 2;
            if (hasMultipleBranches && // Filter out branch conditions which don't split the tree. E.g. The number of applied rules during one step simplification
                !(parentToAddTo instanceof ISEDThread) && // Ignore branch conditions before starting with code execution
                hasBranchCondition(visitedNode) &&
                !isInImplicitMethod(visitedNode)) { // Check if the child has a branch condition
               if (!visitedNode.isClosed()) { // Filter out branches that are closed
                  // Create branch condition
                  ISEDBranchCondition condition = createBranchConditionNode(parentToAddTo, visitedNode.getNodeInfo());
                  // Add branch condition to the branch condition attributes for later adding to the proof tree. This is required for instance to filter out branches after the symbolic execution has finished.
                  List<ISEDBranchCondition> list = parentToBranchConditionMapping.get(parentToAddTo);
                  if (list == null) {
                     list = new LinkedList<ISEDBranchCondition>();
                     branchConditionsStack.addFirst(new DefaultEntry<ISEDDebugNode, List<ISEDBranchCondition>>(parentToAddTo, list));
                     parentToBranchConditionMapping.put(parentToAddTo, list);
                  }
                  list.add(condition);
                  // Transform the current node into a debug node if possible
                  parentToAddTo = analyzeNode(visitedNode, condition);
                  addToMapping.put(visitedNode, parentToAddTo);
               }
            }
            else {
               // No branch condition, transform the current node into a debug node if possible
               parentToAddTo = analyzeNode(visitedNode, parentToAddTo);
               addToMapping.put(visitedNode, parentToAddTo);
            }
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
         }
      }
      
      /**
       * <p>
       * Completes the debug model after all {@link Node}s were visited
       * in {@link #visit(Proof, Node)}. The task of this method is to add
       * {@link ISEDBranchCondition} to the model if they have at least one child.
       * </p>
       * <p>
       * Fore more details have a look at the documentation of {@link #branchConditionsStack}.
       * </p>
       * @throws DebugException Occurred Exception
       */
      public void completeTree() throws DebugException {
          for (Entry<ISEDDebugNode, List<ISEDBranchCondition>> entry : branchConditionsStack) {
             for (ISEDBranchCondition condition : entry.getValue()) {
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
    * filling the contained default {@link ISEDThread} of this {@link ISEDDebugTarget}
    * with {@link ISEDDebugNode}s which are instantiated if a {@link Node}
    * in KeY's proof tree applies a rule of symbolic execution.
    * </p>
    * <p>
    * <b>Attention :</b> A correct pruning requires at the moment that
    * the Taclet Option "runtimeExceptions" is set to "runtimeExceptions:allow".
    * Alternatively it is required to modify rule {@code assignment_to_reference_array_component}
    * in file {@code javaRules.key} by uncommenting {@code \add (!(#v=null) & lt(#se, length(#v)) & geq(#se,0) & arrayStoreValid(#v, #se0)==>)}. 
    * </p>
    * @param node The {@link Node} to analyze.
    * @param parentToAddTo The parent {@link ISEDDebugNode} to add the created debug model representation ({@link ISEDDebugNode}) of the given {@link Node} to.
    * @return The {@link ISEDDebugNode} to which children of the current {@link Node} should be added. If no debug model representation was created the return value is identical to the given one (parentToAddTo).
    * @throws DebugException Occurred Exception.
    */
   protected ISEDDebugNode analyzeNode(Node node, ISEDDebugNode parentToAddTo) throws DebugException {
      // Analyze node
      if (!node.isClosed()) { // Prune closed branches because they are invalid
         // Get required information
         NodeInfo info = node.getNodeInfo();
         SourceElement statement = info.getActiveStatement();
         // Update call stack
         updateCallStack(node, info, statement);
         // Check if the node is already contained in the symbolic execution tree
         ISEDDebugNode debugNode = keyNodeMapping.get(node);
         if (debugNode == null) {
            // Try to create a new node
            debugNode = createDebugModelRepresentation(parentToAddTo, node, info, statement);
            // Check if a new node was created
            if (debugNode != null) {
               // Add new node to symbolic execution tree
               addChild(parentToAddTo, debugNode);
               keyNodeMapping.put(node, debugNode);
               parentToAddTo = debugNode;
            }
         }
         else {
            parentToAddTo = debugNode;
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
               ISEDLoopCondition condition = keyNodeLoopConditionMapping.get(node);
               if (condition == null) {
                  condition = createLoopCondition(parentToAddTo, loop, expression);
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
    * Creates a new debug model representation ({@link ISEDDebugNode}) 
    * if possible for the given {@link Node} in KeY's proof tree.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param node The {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The actual statement ({@link SourceElement}).
    * @return The created {@link ISEDDebugNode} or {@code null} if the {@link Node} should be ignored in the symbolic execution debugger (SED).
    * @throws DebugException Occurred Exception.
    */
   protected ISEDDebugNode createDebugModelRepresentation(ISEDDebugNode parent,
                                                          Node node, 
                                                          NodeInfo info, 
                                                          SourceElement statement) throws DebugException {
      ISEDDebugNode result = null;
      // Make sure that a statement (SourceElement) is available.
      if (statement != null) {
         // Get position information
         PositionInfo posInfo = statement.getPositionInfo();
         // Determine the node representation and create it if one is available
         if (isMethodCallNode(node, info, statement)) {
            Assert.isTrue(statement instanceof MethodBodyStatement, "isMethodCallNode has to verify that the statement is an instance of MethodBodyStatement");
            MethodBodyStatement mbs = (MethodBodyStatement)statement;
            result = createMethodCallNode(node, parent, mbs, posInfo);
         }
         else if (isMethodReturnNode(node, info, statement, posInfo)) {
            // Find the Node in the proof tree of KeY for that this Node is the return
            Node callNode = findMethodCallNode(node);
            if (callNode != null) {
               // Find the call Node representation in SED, if not available ignore it.
               ISEDDebugNode callSEDNode = keyNodeMapping.get(callNode);
               if (callSEDNode != null) {
                  Assert.isTrue(callSEDNode instanceof ISEDMethodCall);
                  result = createMethodReturnNode(parent, node, statement, posInfo, callNode, (ISEDMethodCall)callSEDNode);
               }
            }
         }
         else if (isTerminationNode(node, info, statement, posInfo)) {
            result = createTerminationNode(parent, statement, posInfo);
         }
         else if (isBranchNode(node, info, statement, posInfo)) {
            result = createBranchNode(parent, statement, posInfo);
         }
         else if (isLoopNode(node, info, statement, posInfo)) {
            result = createLoopNode(parent, statement, posInfo);
         }
         else if (isStatementNode(node, info, statement, posInfo)) {
            result = createStatementNode(parent, statement, posInfo);
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
      return false; // TODO: Implement this method to filter out branch conditions
   }

   /**
    * Checks if the given {@link Node} has a branch condition.
    * @param node The {@link Node} to check.
    * @return {@code true} has branch condition, {@code false} has no branch condition.
    */
   protected boolean hasBranchCondition(Node node) {
      NodeInfo info = node.getNodeInfo();
      if (info != null) {
         return !StringUtil.isEmpty(info.getBranchLabel());
      }
      else {
         return false;
      }
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
    * Creates a new {@link ISEDBranchCondition} for the given {@link NodeInfo}.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param info The given {@link NodeInfo} to represent as {@link ISEDBranchCondition}.
    * @return The created {@link ISEDBranchCondition}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDBranchCondition createBranchConditionNode(ISEDDebugNode parent,
                                                           NodeInfo info) throws DebugException {
      // Compute method name
      String name = info.getBranchLabel();
      // Create new node and fill it
      SEDMemoryBranchCondition newNode = new SEDMemoryBranchCondition(getDebugTarget(), parent);
      newNode.setName(name);
      return newNode;
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
    * Creates a new {@link ISEDTermination} for the given {@link SourceElement}.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDTermination}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDTermination}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDTermination createTerminationNode(ISEDDebugNode parent, 
                                                   SourceElement statement, 
                                                   PositionInfo posInfo) throws DebugException {
      // Compute method name
      String name = DEFAULT_TERMINATION_NODE_NAME;
      // Create new node and fill it
      SEDMemoryTermination newNode = new SEDMemoryTermination(getDebugTarget(), parent);
      newNode.setName(name);
      return newNode;
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
      return methodCallStack.get(returnStackSize);
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
    * Creates a new {@link ISEDMethodReturn} for the given {@link SourceElement}.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param node The {@link Node} in the proof tree of KeY.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDStatement}.
    * @param posInfo The {@link PositionInfo} to use.
    * @param callNode The {@link Node} in the proof tree of KeY that has called the method which is now returned.
    * @param callSEDNode The {@link ISEDDebugNode} which represents the method call of the call Node in KeY.
    * @return The created {@link ISEDMethodCall}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDMethodReturn createMethodReturnNode(ISEDDebugNode parent, 
                                                     Node node, 
                                                     SourceElement statement, 
                                                     PositionInfo posInfo,
                                                     Node callNode,
                                                     ISEDMethodCall callSEDNode) throws DebugException {
//      // Find last return node
//      Node returnNode = KeYUtil.findParent(node, new IFilter<Node>() {
//         @Override
//         public boolean select(Node element) {
//            return "methodCallReturn".equals(KeYUtil.getRuleDisplayName(element));
//         }
//      });
//      // Make sure that the return node is a child of the call node and not of a call earlier in the call stack
//      if (!KeYUtil.hasParent(returnNode, callNode)) {
//         returnNode = null;
//      }
      
      // Compute return value
      Object returnValue = null;
//      if (callNode != null) {
//         MethodBodyStatement mbs = (MethodBodyStatement)callNode.getNodeInfo().getActiveStatement();
//         IProgramVariable resultVar = mbs.getResultVariable();
//         if (resultVar != null) {
            // TODO: Compute result value with a side proof in that the result variable is assigned with correct SIMPLIFIED value.
//            returnValue = getValue(node.parent().parent(), resultVar);
//         }
//      }
      // Compute method name
      String name = createMethodReturnName(returnValue, callSEDNode.getName());
      // Create new node and fill it
      SEDMemoryMethodReturn newNode = new SEDMemoryMethodReturn(getDebugTarget(), parent, thread);
      fillNode(newNode, name, posInfo);
      // Update location with the location provided by the call node
      Assert.isTrue(callSEDNode instanceof ISourceNameProvider);
      newNode.setSourceName(((ISourceNameProvider)callSEDNode).getSourceName());
      newNode.setLineNumber(callSEDNode.getLineNumber());
      newNode.setCharStart(callSEDNode.getCharStart());
      newNode.setCharEnd(callSEDNode.getCharEnd());
      return newNode;
   }

//   protected Object getValue(Node node, IProgramVariable var) {
//      Object result = null;
//      PosInOccurrence posInOccurrence = node.getAppliedRuleApp().posInOccurrence();
//      Term currentTerm = posInOccurrence.constrainedFormula().formula();
//      // Make sure that the sequence has the expected form
//      if (currentTerm.op() instanceof UpdateApplication) {
//         if (currentTerm.sub(1).op() instanceof Modality &&
//             posInOccurrence.subTerm() == currentTerm.sub(1)) {
//            Term updateToApply = currentTerm.sub(0);
//            result = getValue(updateToApply, var);
//         }
//      }
//      return result;
//   }
//   
//   protected Object getValue(Term term, IProgramVariable var) {
//      Object result = null;
//      if (term.op() instanceof UpdateJunctor) {
//         // Parallel updates
//         Iterator<Term> subTermsIter = term.subs().iterator();
//         while (result == null && subTermsIter.hasNext()) {
//            Term subTerm = subTermsIter.next();
//            result = getValue(subTerm, var);
//         }
//      }
//      else if (term.op() instanceof ElementaryUpdate) {
//         // Elementary update
//         ElementaryUpdate operator = (ElementaryUpdate)term.op();
//         if (ObjectUtil.equals(var, operator.lhs())) {
//            result = term.sub(0);
//         }
//      }
//      return result;
//   }

   /**
    * Creates the human readable name which is shown in {@link ISEDMethodReturn} instances.
    * @param returnValue The return value.
    * @param methodName The name of the method that is completely executed.
    * @return The created human readable name.
    */
   public static String createMethodReturnName(Object returnValue, String methodName) {
      return INTERNAL_NODE_START + "return" +
             (returnValue != null ? " " + returnValue + " as result" : StringUtil.EMPTY_STRING) +
             (!StringUtil.isTrimmedEmpty(methodName) ? " of " + methodName : StringUtil.EMPTY_STRING) +
             INTERNAL_NODE_END;
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
    * Creates a new {@link ISEDMethodCall} for the given {@link MethodBodyStatement}.
    * @param node The current {@link Node} in KeY's proof tree.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param statement The given {@link MethodBodyStatement} to represent as {@link ISEDMethodCall}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDMethodCall}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDMethodCall createMethodCallNode(Node node,
                                                 ISEDDebugNode parent, 
                                                 MethodBodyStatement mbs, 
                                                 PositionInfo posInfo) throws DebugException {
      // Compute method name
      MethodReference mr = mbs.getMethodReference();
      ProgramMethod pm = mbs.getProgramMethod(proof.getServices());
      String name = mr != null ? mr.toString() : UNKNOWN_METHOD_NAME;
      // Create new node and fill it
      SEDMemoryMethodCall newNode = new SEDMemoryMethodCall(getDebugTarget(), parent, thread);
      fillNode(newNode, name, pm.getPositionInfo());
      // Try to update the position info with the position of the method name provided by JDT.
      try {
         if (newNode.getCharEnd() >= 0) {
            ICompilationUnit compilationUnit = findCompilationUnit(newNode);
            if (compilationUnit != null) {
               IMethod method = findJDTMethod(compilationUnit, newNode.getCharEnd());
               if (method != null) {
                  ISourceRange range = method.getNameRange();
                  newNode.setLineNumber(-1);
                  newNode.setCharStart(range.getOffset());
                  newNode.setCharEnd(range.getOffset() + range.getLength());
               }
            }
         }
      }
      catch (Exception e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
      return newNode;
   }
   
   /**
    * Tries to find an {@link ICompilationUnit} for the given {@link IStackFrame}.
    * @param frame The given {@link IStackFrame} for that is an {@link ICompilationUnit} required.
    * @return The found {@link ICompilationUnit}.
    */
   protected ICompilationUnit findCompilationUnit(IStackFrame frame) {
      ICompilationUnit result = null;
      if (frame != null) {
         Object source = getLaunch().getSourceLocator().getSourceElement(frame);
         if (source instanceof IFile) {
            IJavaElement element = JavaCore.create((IFile)source);
            if (element instanceof ICompilationUnit) {
               result = (ICompilationUnit)element;
            }
         }
      }
      return result;
   }
   
   /**
    * Searches the {@link IMethod} as JDT representation which ends
    * at the given index.
    * @param cu The {@link ICompilationUnit} to search in.
    * @param endIndex The index in the file at that the required method ends.
    * @return The found {@link IMethod} or {@code null} if the JDT representation is not available.
    * @throws JavaModelException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public IMethod findJDTMethod(ICompilationUnit cu, int endIndex) throws JavaModelException, IOException {
      IMethod result = null;
      if (cu != null) {
         IType[] types = cu.getAllTypes();
         int i = 0;
         while (result == null && i < types.length) {
            IMethod[] methods = types[i].getMethods();
            int j = 0;
            while (result == null && j < methods.length) {
               ISourceRange methodRange = methods[j].getSourceRange();
               if (endIndex == methodRange.getOffset() + methodRange.getLength()) {
                  result = methods[j];
               }
               j++;
            }
            i++;
         }
      }
      return result;
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
    * Creates a new {@link ISEDLoopNode} for the given {@link SourceElement}.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDLoopNode}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDLoopNode}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDLoopNode createLoopNode(ISEDDebugNode parent, 
                                         SourceElement statement, 
                                         PositionInfo posInfo) throws DebugException {
      // Compute statement name
      String name = statement.toString();
      // Create new node and fill it
      SEDMemoryLoopNode newNode = new SEDMemoryLoopNode(getDebugTarget(), parent, thread);
      fillNode(newNode, name, posInfo);
      // Try to update the position info with the position of the statement in JDT.
      updateLocationFromAST(newNode);
      return newNode;
   }
   
   /**
    * Creates a new {@link ISEDLoopCondition} for the given {@link SourceElement}.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param statement The given {@link LoopStatement} to represent as {@link ISEDLoopCondition}.
    * @param expression The {@link Expression} of the {@link LoopStatement}.
    * @return The created {@link ISEDLoopCondition}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDLoopCondition createLoopCondition(ISEDDebugNode parent, 
                                                   LoopStatement statement,
                                                   Expression expression) throws DebugException {
      // Get the position
      PositionInfo posInfo = expression.getPositionInfo();
      // Compute statement name
      String name = ObjectUtil.toString(expression);
      // Create new node and fill it
      SEDMemoryLoopCondition newNode = new SEDMemoryLoopCondition(getDebugTarget(), parent, thread);
      fillNode(newNode, name, posInfo);
      // Try to update the position info with the position of the statement in JDT.
      updateLocationFromAST(newNode);
      // Boolean literals have no position info, set the file of the statement without location in this case
      if (newNode.getSourceName() == null) {
         if (statement.getPositionInfo().getFileName() != null) {
            File file = new File(statement.getPositionInfo().getFileName());
            newNode.setSourceName(file.getName());
         }
      }
      return newNode;
   }
   
   /**
    * Creates a new {@link ISEDBranchNode} for the given {@link SourceElement}.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDBranchNode}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDBranchNode}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDBranchNode createBranchNode(ISEDDebugNode parent, 
                                             SourceElement statement, 
                                             PositionInfo posInfo) throws DebugException {
      // Compute statement name
      String name = statement.toString();
      // Create new node and fill it
      SEDMemoryBranchNode newNode = new SEDMemoryBranchNode(getDebugTarget(), parent, thread);
      fillNode(newNode, name, posInfo);
      // Try to update the position info with the position of the statement in JDT.
      updateLocationFromAST(newNode);
      return newNode;
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
    * Creates a new {@link ISEDStatement} for the given {@link SourceElement}.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDStatement}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDStatement}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDStatement createStatementNode(ISEDDebugNode parent, 
                                               SourceElement statement, 
                                               PositionInfo posInfo) throws DebugException {
      // Compute statement name
      String name = statement.toString();
      // Create new node and fill it
      SEDMemoryStatement newNode = new SEDMemoryStatement(getDebugTarget(), parent, thread);
      fillNode(newNode, name, posInfo);
      // Try to update the position info with the position of the statement in JDT.
      updateLocationFromAST(newNode);
      return newNode;
   }
   
   /**
    * Replaces the location in the given {@link ISEDMemoryStackFrameCompatibleDebugNode}
    * if possible with the location provided via JDT AST model which is more precise.
    * @param newNode The {@link ISEDMemoryStackFrameCompatibleDebugNode} to update.
    * @throws DebugException Occurred Exception.
    */
   protected void updateLocationFromAST(ISEDMemoryStackFrameCompatibleDebugNode newNode) throws DebugException {
      try {
         if (newNode.getCharEnd() >= 0) {
            ICompilationUnit compilationUnit = findCompilationUnit(newNode);
            if (compilationUnit != null) {
               ASTNode root = parse(compilationUnit, newNode.getCharStart(), newNode.getCharEnd() - newNode.getCharStart());
               ASTNode statementNode = ASTNodeByEndIndexSearcher.search(root, newNode.getCharEnd());
               if (statementNode != null) {
                  newNode.setLineNumber(-1);
                  newNode.setCharStart(statementNode.getStartPosition());
                  newNode.setCharEnd(statementNode.getStartPosition() + statementNode.getLength());
               }
            }
         }
      }
      catch (Exception e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
   }
   
   /**
    * Parses the given {@link ICompilationUnit} in the specified range into an AST. 
    * @param compilationUnit The {@link ICompilationUnit} to parse.
    * @param offset The start index in the text to parse.
    * @param length The length of the text to parse.
    * @return The {@link ASTNode} which is the root of the AST.
    */
   protected ASTNode parse(ICompilationUnit compilationUnit, int offset, int length) {
      ASTParser parser = ASTParser.newParser(ASTProvider.SHARED_AST_LEVEL); // Hopefully always the newest AST level (e.g. AST.JLS4)
      parser.setSource(compilationUnit);
      parser.setSourceRange(offset, length);
      return parser.createAST(null);
   }
   
   /**
    * Fills the given {@link ISEDMemoryStackFrameCompatibleDebugNode} with the position information.
    * @param toFill The {@link ISEDMemoryStackFrameCompatibleDebugNode} to fill.
    * @param name The name to set.
    * @param posInfo The {@link PositionInfo} to set.
    * @throws DebugException Occurred Exception.
    */
   protected void fillNode(ISEDMemoryStackFrameCompatibleDebugNode toFill, String name, PositionInfo posInfo) throws DebugException {
      try {
         Assert.isNotNull(toFill);
         toFill.setName(name);
         if (posInfo != null && posInfo != PositionInfo.UNDEFINED) {
            // Try to find the source file.
            File file = null;
            if (posInfo.getFileName() != null) {
               file = new File(posInfo.getFileName());
            }
            else if (posInfo.getParentClass() != null) {
               file = new File(posInfo.getParentClass());
            }
            // Check if a source file is available
            if (file != null) {
               // Store reference to source file
               toFill.setSourceName(file.getName());
               // Set source location
               LineInformation[] infos = IOUtil.computeLineInformation(file);
               if (posInfo.getStartPosition() != null) {
                  int line = posInfo.getStartPosition().getLine() - 1;
                  int column = posInfo.getStartPosition().getColumn();
                  if (line >= 0 && line < infos.length) {
                     LineInformation info = infos[line];
                     int offset = info.getOffset() + KeYUtil.normalizeRecorderColumn(column, info.getTabIndices());
                     toFill.setCharStart(offset);
                  }
               }
               if (posInfo.getEndPosition() != null) {
                  int line = posInfo.getEndPosition().getLine() - 1;
                  int column = posInfo.getEndPosition().getColumn();
                  if (line >= 0 && line < infos.length) {
                     LineInformation info = infos[line];
                     int offset = info.getOffset() + KeYUtil.normalizeRecorderColumn(column, info.getTabIndices());
                     toFill.setCharEnd(offset);
                  }
               }
            }
            // Check if source start and end is defined.
            if (toFill.getCharStart() < 0 || toFill.getCharEnd() < 0) {
               // Unset start and end indices
               toFill.setCharStart(-1);
               toFill.setCharEnd(-1);
               // Try to set a line number as backup
               if (posInfo.getEndPosition() != null) {
                  toFill.setLineNumber(posInfo.getEndPosition().getLine());
               }
            }
         }
      }
      catch (IOException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
   }
   
   /**
    * Adds the child to the parent.
    * @param parent The parent to add to.
    * @param child The child to add.
    */
   protected void addChild(ISEDDebugNode parent, ISEDDebugNode child) {
      if (parent instanceof ISEDMemoryDebugNode) {
         ((ISEDMemoryDebugNode)parent).addChild(child);
      }
      else {
         throw new IllegalArgumentException("Unsupported parent \"" + parent + "\".");
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      // Remove auto mode listener
      MainWindow main = MainWindow.getInstance(); 
      main.getMediator().removeAutoModeListener(autoModeListener);
      // Suspend first to stop the automatic mode
      if (!isSuspended()) {
         suspend();
         KeYUtil.waitWhileMainWindowIsFrozen(main);
      }
      // Remove proof from user interface
      KeYUtil.removeFromProofList(main, proof.env());
      // Clear cache
      keyNodeMapping.clear();
      keyNodeLoopConditionMapping.clear();
      loopExpressionToLoopStatementMapping.clear();
      methodCallStack.clear();
      // Inform UI that the process is terminated
      super.terminate();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnect() throws DebugException {
      // Remove auto mode listener
      MainWindow.getInstance().getMediator().removeAutoModeListener(autoModeListener);
      // Inform UI that the process is disconnected
      super.disconnect();
   }

   /**
    * When the auto mode is started.
    * @param e The event.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      try {
         if (e.getSource() == proof) {
            // Inform UI that the process is resumed
            super.resume();
         }
      }
      catch (DebugException exception) {
         LogUtil.getLogger().logError(exception);
      }
   }

   /**
    * When the auto mode has stopped.
    * @param e The event.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      try {
         if (e.getSource() == proof) {
            analyzeProof(proof);
            super.suspend();
         }
      }
      catch (Exception exception) {
         LogUtil.getLogger().logError(exception);
         LogUtil.getLogger().openErrorDialog(null, exception);
      }
   }
}
