package org.key_project.sed.key.core.model;

import java.io.File;
import java.io.IOException;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
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
import org.key_project.key4eclipse.starter.core.util.NodePreorderIterator;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
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
import org.key_project.sed.core.model.memory.SEDMemoryExceptionalTermination;
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
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
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
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProofStarter;

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
    * Contains the exception variable which is used to check if the executed program in proof terminates normally.
    */
   private IProgramVariable exceptionVariable;
   
   /**
    * Constructor.
    * @param launch The parent {@link ILaunch}.
    * @param proof The {@link Proof} in KeY to treat.
    * @throws DebugException Occurred Exception
    */
   public KeYDebugTarget(ILaunch launch, Proof proof) throws DebugException {
      super(launch);
      // Update references
      Assert.isNotNull(proof);
      this.proof = proof;
      this.exceptionVariable = extractExceptionVariable(proof);
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
    * Extracts the exception variable which is used to check if the executed program in proof terminates normally.
    * @param proof The {@link Proof} to extract variable from.
    * @return The extract variable.
    * @throws DebugException Thrown exception if the exception variable was not found.
    */
   protected IProgramVariable extractExceptionVariable(Proof proof) throws DebugException {
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
      throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't extract exception variable from proof."));
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
      NodePreorderIterator iter = new NodePreorderIterator(proof.root());
      while (iter.hasNext()) {
         visitor.visit(proof, iter.next()); // This visitor pattern must be used because a recursive iteration causes StackOverflowErrors if the proof tree in KeY is to deep (e.g. simple list with 2000 elements during computation of fibonacci(7)
      }
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
       * Maps the {@link Node} with branch conditions in KeY's proof tree to the {@link ISEDDebugNode} of the debugger where the {@link Node}s children should be added to.
       */
      private Map<Node, ISEDDebugNode> branchConditionAddToMapping = new HashMap<Node, ISEDDebugNode>();
      
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
            ISEDDebugNode parentToAddTo = branchConditionAddToMapping.get(visitedNode);
            if (parentToAddTo == null) {
               Node parent = visitedNode.parent(); 
               if (parent != null) {
                  parentToAddTo = addToMapping.get(parent);
               }
               else {
                  parentToAddTo = thread;
               }
            }
            // transform the current node into a debug node if possible
            parentToAddTo = analyzeNode(visitedNode, parentToAddTo);
            addToMapping.put(visitedNode, parentToAddTo);
            // Check if the current node has branch conditions which should be added to the debug model
            if (!(parentToAddTo instanceof ISEDThread) && // Ignore branch conditions before starting with code execution
                hasBranchCondition(visitedNode)) {
               NodeIterator iter = visitedNode.childrenIterator();
               while (iter.hasNext()) {
                  Node childNode = iter.next();
                  if (!visitedNode.isClosed()) { // Filter out branches that are closed
                     // Create branch condition
                     ISEDBranchCondition condition = createBranchConditionNode(parentToAddTo, childNode.getNodeInfo());
                     // Add branch condition to the branch condition attributes for later adding to the proof tree. This is required for instance to filter out branches after the symbolic execution has finished.
                     List<ISEDBranchCondition> list = parentToBranchConditionMapping.get(parentToAddTo);
                     if (list == null) {
                        list = new LinkedList<ISEDBranchCondition>();
                        branchConditionsStack.addFirst(new DefaultEntry<ISEDDebugNode, List<ISEDBranchCondition>>(parentToAddTo, list));
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
            String exceptionSort = extractExceptionSort(node);
            if (exceptionSort != null) {
               result = createExceptionalTerminationNode(exceptionSort, parent, statement, posInfo);
            }
            else {
               result = createTerminationNode(parent, statement, posInfo);
            }
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
      Node callNode = findMethodCallNode(node);
      if (callNode != null) {
         NodeInfo callInfo = callNode.getNodeInfo();
         SourceElement callStatement = callInfo.getActiveStatement();
         return !isMethodCallNode(callNode, callInfo, callStatement);
      }
      else {
         return true;
      }
   }

   /**
    * Checks if the given {@link Node} has a branch condition.
    * @param node The {@link Node} to check.
    * @return {@code true} has branch condition, {@code false} has no branch condition.
    * @throws DebugException Occurred Exception
    */
   protected boolean hasBranchCondition(Node node) throws DebugException {
      if (node.childrenCount() >= 2) { // Check if it is a possible branch node, otherwise there is no need for complex computation to filter out not relevant branches
         int openChildrenCount = 0;
         NodeIterator childIter = node.childrenIterator();
         while (childIter.hasNext()) {
            Node child = childIter.next();
            // Make sure that the branch is not closed
            if (!child.isClosed()) {
               // Check if the current method on stack is not an implicit method
               Node nextSymbolicExecutionNode = searchLinearNextSymbolicExecutionNode(child);
               if (!isInImplicitMethod(nextSymbolicExecutionNode)) { // Ignore branch conditions from implicit methods (requires runtime option eagerSplitting: on)
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
    * @throws DebugException Thrown {@link Exception} if the children branches before a symbolic statement was applied.
    */
   protected Node searchLinearNextSymbolicExecutionNode(Node node) throws DebugException {
      while (node != null && node.getNodeInfo().getActiveStatement() == null) {
         int childCount = node.childrenCount();
         if (childCount == 0) {
            node = null;
         }
         else if (childCount == 1) {
            node = node.child(0);
         }
         else {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Assumption that after a split a symoblic execution is done before a branch occurre does not hold."));
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
      SEDMemoryBranchCondition newNode = new SEDMemoryBranchCondition(getDebugTarget(), parent, thread);
      newNode.setName(name);
      return newNode;
   }
   

   protected String extractExceptionSort(Node terminationNode) throws DebugException {
      String result = null;
      if (terminationNode != null) {
         // Search final value of the exceptional variable which is used to check if the verified program terminates normally
         ImmutableArray<Term> value = null;
         for (SequentFormula f : terminationNode.sequent().succedent()) {
            Pair<ImmutableList<Term>,Term> updates = MiscTools.goBelowUpdates2(f.formula());
            Iterator<Term> iter = updates.first.iterator();
            while (value == null && iter.hasNext()) {
               value = extractValueFromUpdate(iter.next(), exceptionVariable);
            }
         }
         // An exceptional termination is found if the exceptional variable is not null
         if (value != null && value.size() == 1) {
            Sort sort = value.get(0).sort();
            if (sort != null && !(sort instanceof NullSort)) {
               result = sort.toString();
            }
         }
      }
      return result;
   }
   
   /**
    * Utility method to extract the value of the {@link IProgramVariable}
    * from the given update term.
    * @param term The given update term.
    * @param variable The {@link IProgramVariable} for that the value is needed.
    * @return The found value or {@code null} if it is not defined in the given update term.
    */
   protected ImmutableArray<Term> extractValueFromUpdate(Term term,
                                                         IProgramVariable variable) {
      ImmutableArray<Term> result = null;
      if (term.op() instanceof ElementaryUpdate) {
         ElementaryUpdate update = (ElementaryUpdate)term.op();;
         if (ObjectUtil.equals(variable, update.lhs())) {
            result = term.subs();
         }
      }
      else if (term.op() instanceof UpdateJunctor) {
         Iterator<Term> iter = term.subs().iterator();
         while (result == null && iter.hasNext()) {
            result = extractValueFromUpdate(iter.next(), variable);
         }
      }
      return result;
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
    * Creates a new {@link ISEDExceptionalTermination} for the given {@link SourceElement}.
    * @param exceptionSort The sort of the thrown exception.
    * @param parent The parent {@link ISEDDebugNode}.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDExceptionalTermination}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDExceptionalTermination}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDExceptionalTermination createExceptionalTerminationNode(String exceptionSort,
                                                                         ISEDDebugNode parent, 
                                                                         SourceElement statement, 
                                                                         PositionInfo posInfo) throws DebugException {
      Assert.isNotNull(exceptionSort);
      // Compute method name
      String name = INTERNAL_NODE_START + "uncaught " + exceptionSort + INTERNAL_NODE_END;
      // Create new node and fill it
      SEDMemoryExceptionalTermination newNode = new SEDMemoryExceptionalTermination(getDebugTarget(), parent, thread);
      newNode.setName(name);
      return newNode;
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
      SEDMemoryTermination newNode = new SEDMemoryTermination(getDebugTarget(), parent, thread);
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
   // TODO: Return value can be unknown in SET, e.g. quotient in TryCatchFinally test
   protected ISEDMethodReturn createMethodReturnNode(ISEDDebugNode parent, 
                                                     Node node, 
                                                     SourceElement statement, 
                                                     PositionInfo posInfo,
                                                     Node callNode,
                                                     ISEDMethodCall callSEDNode) throws DebugException {
      // Compute return value if possible
      Object returnValue = null;
      if (callNode != null) {
         // Check if a result variable is available
         MethodBodyStatement mbs = (MethodBodyStatement)callNode.getNodeInfo().getActiveStatement();
         IProgramVariable resultVar = mbs.getResultVariable();
         if (resultVar != null) {
            // Search the node with applied rule "methodCallReturn" which provides the required updates
            Node methodReturnNode = findMethodReturnNode(node);
            if (methodReturnNode != null) {
               // Start site proof to extract the value of the result variable.
               SiteProofVariableValueInput sequentToProve = createExtractVariableValueSequent(mbs.getBodySourceAsTypeReference(),  
                                                                                              mbs.getDesignatedContext(), 
                                                                                              methodReturnNode, 
                                                                                              resultVar);
               ApplyStrategy.ApplyStrategyInfo info = startSiteProof(sequentToProve.getSequentToProve());
               returnValue = extractOperatorValue(info, sequentToProve.getOperator());
            }
         }
      }
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
   
   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param contextObjectType The type of the current object (this reference).
    * @param contextObject The current object (this reference).
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   protected SiteProofVariableValueInput createExtractVariableValueSequent(TypeReference contextObjectType,
                                                                           ReferencePrefix contextObject,
                                                                           Node node,
                                                                           IProgramVariable variable) {
      // Create execution context in that the method was called.
      IExecutionContext context = new ExecutionContext(contextObjectType, contextObject);
      // Create sequent
      return createExtractVariableValueSequent(context, node, variable);
   }

   /**
    * Creates a {@link Sequent} which can be used in site proofs to
    * extract the value of the given {@link IProgramVariable} from the
    * sequent of the given {@link Node}.
    * @param context The {@link IExecutionContext} that defines the current object (this reference).
    * @param node The original {@link Node} which provides the sequent to extract from.
    * @param variable The {@link IProgramVariable} of the value which is interested.
    * @return The created {@link SiteProofVariableValueInput} with the created sequent and the predicate which will contain the value.
    */
   protected SiteProofVariableValueInput createExtractVariableValueSequent(IExecutionContext context,
                                                                           Node node,
                                                                           IProgramVariable variable) {
      // Make sure that correct parameters are given
      Assert.isNotNull(context);
      Assert.isNotNull(node);
      Assert.isTrue(variable instanceof ProgramVariable);
      // Create method frame which will be executed in site proof
      Statement originalReturnStatement = (Statement)node.getNodeInfo().getActiveStatement();
      MethodFrame newMethodFrame = new MethodFrame(variable, context, new StatementBlock(originalReturnStatement));
      JavaBlock newJavaBlock = JavaBlock.createJavaBlock(new StatementBlock(newMethodFrame));
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(TermBuilder.DF.newName(proof.getServices(), "ResultPredicate")), Sort.FORMULA, variable.sort());
      // Create formula which contains the value interested in.
      Term newTerm = TermBuilder.DF.func(newPredicate, TermBuilder.DF.var((ProgramVariable)variable));
      // Combine method frame with value formula in a modality.
      Term modalityTerm = TermBuilder.DF.dia(newJavaBlock, newTerm);
      // Get the updates from the return node which includes the value interested in.
      Term originalModifiedFormula = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
      ImmutableList<Term> originalUpdates = MiscTools.goBelowUpdates2(originalModifiedFormula).first;
      // Combine method frame, formula with value predicate and the updates which provides the values
      Term newSuccedentToProve = TermBuilder.DF.applySequential(originalUpdates, modalityTerm);
      // Create new sequent with the original antecedent and the formulas in the succedent which were not modified by the applied rule
      PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
      Sequent originalSequentWithoutMethodFrame = node.sequent().removeFormula(pio).sequent();
      Sequent sequentToProve = originalSequentWithoutMethodFrame.addFormula(new SequentFormula(newSuccedentToProve), false, true).sequent();
      // Return created sequent and the used predicate to identify the value interested in.
      return new SiteProofVariableValueInput(sequentToProve, newPredicate);
   }
   
   /**
    * Helper class which represents the return value of
    * {@link KeYDebugTarget#createExtractVariableValueSequent(TypeReference, ReferencePrefix, Node, IProgramVariable)} and
    * {@link KeYDebugTarget#createExtractVariableValueSequent(IExecutionContext, Node, IProgramVariable)}.
    * @author Martin Hentschel
    */
   protected static class SiteProofVariableValueInput {
      /**
       * The sequent to prove.
       */
      private Sequent sequentToProve;
      
      /**
       * The {@link Operator} which is the predicate that contains the value interested in.
       */
      private Operator operator;
      
      /**
       * Constructor.
       * @param sequentToProve he sequent to prove.
       * @param operator The {@link Operator} which is the predicate that contains the value interested in.
       */
      public SiteProofVariableValueInput(Sequent sequentToProve, Operator operator) {
         super();
         this.sequentToProve = sequentToProve;
         this.operator = operator;
      }
      
      /**
       * Returns the sequent to prove.
       * @return The sequent to prove.
       */
      public Sequent getSequentToProve() {
         return sequentToProve;
      }
      
      /**
       * Returns the {@link Operator} which is the predicate that contains the value interested in.
       * @return The {@link Operator} which is the predicate that contains the value interested in.
       */
      public Operator getOperator() {
         return operator;
      }
   }
   
   /**
    * Starts a site proof for the given {@link Sequent}.
    * @param sequentToProve The {@link Sequent} to prove.
    * @return The proof result represented as {@link ApplyStrategyInfo} instance.
    * @throws DebugException Occurred Exception.
    */
   protected ApplyStrategyInfo startSiteProof(Sequent sequentToProve) throws DebugException {
      try {
         // Make sure that valid parameters are given
         Assert.isNotNull(sequentToProve);
         // Create ProofStarter
         ProofStarter starter = new ProofStarter();
         // Configure ProofStarter
         starter.init(sequentToProve, proof.env());
         starter.setMaxRuleApplications(1000);
         StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties(); // Is a clone that can be modified
         sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_OFF); // Logical Splitting: Off
         sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_NONE); // Method Treatement: Off
         sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF); // Dependency Contracts: Off
         sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_OFF); // Query Treatment: Off
         sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS); // Arithmetic Treatment: DefOps
         sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NONE); // Quantifier treatment: All except Free 
         starter.setStrategy(sp);
         // Execute proof in the current thread
         return starter.start();
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
   }
   
   /**
    * Extracts the value for the formula with the given {@link Operator}
    * from the site proof result ({@link ApplyStrategyInfo}).
    * @param info The site proof result.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The value of the formula with the given {@link Operator}.
    * @thorws DebugException Occurred Exception.
    */
   protected String extractOperatorValue(ApplyStrategyInfo info, final Operator operator) throws DebugException {
      // Make sure that valid parameters are given
      Assert.isNotNull(info);
      if (info.getProof().openGoals().size() != 1) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Assumption that return value extraction has one goal does not hold because " + info.getProof().openGoals().size() + " goals are available."));
      }
      // Get node of open goal
      Node goalNode = info.getProof().openGoals().head().node();
      // Search formula with the given operator in sequent
      SequentFormula sf = CollectionUtil.search(goalNode.sequent(), new IFilter<SequentFormula>() {
         @Override
         public boolean select(SequentFormula element) {
            return ObjectUtil.equals(element.formula().op(), operator);
         }
      });
      if (sf != null) {
         // Format found value
         StringBuffer sb = ProofSaver.printTerm(sf.formula().sub(0), info.getProof().getServices(), true);
         return sb.toString();
      }
      else {
         return null;
      }
   }

   /**
    * Searches from the given {@link Node} the parent which applies
    * the rule "methodCallReturn".
    * @param node The {@link Node} to start search from.
    * @return The found {@link Node} with rule "methodCallReturn" or {@code null} if no node was found.
    */
   protected Node findMethodReturnNode(Node node) {
      Node resultNode = null;
      while (node != null && resultNode == null) {
         if ("methodCallReturn".equals(KeYUtil.getRuleDisplayName(node))) {
            resultNode = node;
         }
         node = node.parent();
      }
      return resultNode;
   }

   /**
    * Creates the human readable name which is shown in {@link ISEDMethodReturn} instances.
    * @param returnValue The return value.
    * @param methodName The name of the method that is completely executed.
    * @return The created human readable name.
    */
   public static String createMethodReturnName(Object returnValue, String methodName) {
      return INTERNAL_NODE_START + "return" +
             (returnValue != null ? " '" + returnValue + "' as result" : StringUtil.EMPTY_STRING) +
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
         }
      }
      catch (Exception exception) {
         LogUtil.getLogger().logError(exception);
         LogUtil.getLogger().openErrorDialog(null, exception);
      }
      finally {
         try {
            super.suspend();
         }
         catch (DebugException e1) {
            LogUtil.getLogger().logError(e1);
            LogUtil.getLogger().openErrorDialog(null, e1);
         }
      }
   }
}
