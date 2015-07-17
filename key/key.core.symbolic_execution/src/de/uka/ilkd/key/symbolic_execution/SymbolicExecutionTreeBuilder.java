// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution;

import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.ArrayUtil;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBlockStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination.TerminationKind;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionBlockStartNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionExceptionalMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionLoopStatement;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.impl.TreeSettings;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.DefaultEntry;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.NodePreorderIterator;
import de.uka.ilkd.key.util.Pair;

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
 * of a symbolic execution tree is an {@link IExecutionStart} which is
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
 * @see IExecutionStart
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
   private ExecutionStart startNode;
   
   /**
    * <p>
    * Maps a {@link Node} of KeY's proof tree to his execution tree model representation
    * if it is available.
    * </p>
    * <p>
    * In case that the {@link Node} is represented by multiple {@link AbstractExecutionNode}s,
    * e.g. a return statement and a method return, the last node is returned.
    * </p>
    */
   private Map<Node, AbstractExecutionNode<?>> keyNodeMapping = new LinkedHashMap<Node, AbstractExecutionNode<?>>();
   
   /**
    * Maps a loop condition of a {@link Node} of KeY's proof tree to his 
    * execution tree model representation ({@link IExecutionLoopCondition}) if it is available.
    */
   private Map<Node, ExecutionLoopCondition> keyNodeLoopConditionMapping = new LinkedHashMap<Node, ExecutionLoopCondition>();
   
   /**
    * Maps a branch condition of a {@link Node} of KeY's proof tree to his 
    * execution tree model representation ({@link IExecutionBranchCondition}) if it is available.
    */
   private Map<Node, ExecutionBranchCondition> keyNodeBranchConditionMapping = new LinkedHashMap<Node, ExecutionBranchCondition>();
   
   /**
    * Contains the method call stacks for each tracked symbolic execution modality.
    * As key is {@link SymbolicExecutionTermLabel#getId()} used.
    */
   private Map<Integer, Map<Node, ImmutableList<Node>>> methodCallStackMap = new LinkedHashMap<Integer, Map<Node, ImmutableList<Node>>>();
   
   /**
    * Contains the possible statements after a code block of interest for each tracked symbolic execution modality.
    * As key is {@link SymbolicExecutionTermLabel#getId()} used.
    */
   private Map<Integer, Map<Node, Map<JavaPair, ImmutableList<IExecutionNode<?>>>>> afterBlockMap = new LinkedHashMap<Integer, Map<Node, Map<JavaPair, ImmutableList<IExecutionNode<?>>>>>();

   /**
    * Contains {@link Node}s of method calls which return statements should be ignored. 
    * As key is {@link SymbolicExecutionTermLabel#getId()} used.
    */
   private Map<Integer, Set<Node>> methodReturnsToIgnoreMap = new LinkedHashMap<Integer, Set<Node>>();

   /**
    * Contains the exception variable which is used to check if the executed program in proof terminates normally.
    */
   private IProgramVariable exceptionVariable;
   
   /**
    * The {@link TreeSettings} to use.
    */
   private final TreeSettings settings;
   
   /**
    * {@code true} infeasible paths are closed, {@code false} infeasible may be open may be closed.
    */
   private final boolean isUninterpretedPredicateUsed;
   
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
   private final Deque<Entry<AbstractExecutionNode<?>, List<ExecutionBranchCondition>>> branchConditionsStack = new LinkedList<Entry<AbstractExecutionNode<?>, List<ExecutionBranchCondition>>>();

   /**
    * Constructor.
    * @param proof The {@link Proof} to extract the symbolic execution tree from.
    * @param mergeBranchConditions {@code true} merge branch conditions which means that a branch condition never contains another branch condition or {@code false} allow that branch conditions contains branch conditions.
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @param simplifyConditions {@code true} simplify conditions, {@code false} do not simplify conditions.
    */
   public SymbolicExecutionTreeBuilder(Proof proof,
                                       boolean mergeBranchConditions,
                                       boolean useUnicode,
                                       boolean usePrettyPrinting,
                                       boolean variablesAreOnlyComputedFromUpdates,
                                       boolean simplifyConditions) {
      assert proof != null;
      this.proof = proof;
      this.isUninterpretedPredicateUsed = AbstractOperationPO.getUninterpretedPredicate(getProof()) != null;
      this.settings = new TreeSettings(mergeBranchConditions, useUnicode, usePrettyPrinting, variablesAreOnlyComputedFromUpdates, simplifyConditions);
      this.exceptionVariable = SymbolicExecutionUtil.extractExceptionVariable(proof);
      this.startNode = new ExecutionStart(settings, proof.root());
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
               if (visited.op() instanceof Modality && SymbolicExecutionUtil.hasSymbolicExecutionLabel(visited)) {
                  modalityTerms.add(visited);
               }
            }
         });
      }
      // Make sure that at least one modality was found
      if (modalityTerms.isEmpty()) {
         throw new IllegalStateException("Sequent contains no modalities with symbolic execution label.");
      }
      // Make sure that at most one modality was found
      if (modalityTerms.size() >= 2) {
         throw new IllegalStateException("Sequent contains multiple modalities with symbolic execution label.");
      }
      // Make sure that modality has symbolic execution label
      Term modalityTerm = modalityTerms.get(0);
      SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(modalityTerm);
      if (label == null) {
         throw new IllegalStateException("Modality \"" + modalityTerm + "\" has no symbolic execution term label.");
      }
      // Check if modality contains method frames
      if (!modalityTerms.isEmpty()) {
         JavaBlock javaBlock = modalityTerm.javaBlock();
         final ProgramElement program = javaBlock.program(); 
         final List<Node> initialStack = new LinkedList<Node>();
         new JavaASTVisitor(program, services) {
            @Override
            protected void doDefaultAction(SourceElement node) {
            }
            
            @Override
            public void performActionOnMethodFrame(MethodFrame x) {
               initialStack.add(root);
            }

            public void run() {
               walk(program);
            }
         }.run();
         Map<Node, ImmutableList<Node>> methodCallStack = getMethodCallStack(label);
         methodCallStack.put(root, ImmutableSLList.<Node>nil().append(initialStack));
      }
   }
   
   /**
    * Returns the method {@link Node}s of method calls for
    * which its return should be ignored. If not already
    * available an empty method {@link Set} is created.
    * @param ruleApp The {@link RuleApp} which modifies a modality {@link Term} with a {@link SymbolicExecutionTermLabel}.
    * @return The {@link Set} of {@link Node}s to ignore its return.
    */
   protected Set<Node> getMethodReturnsToIgnore(RuleApp ruleApp) {
      SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(ruleApp);
      return getMethodReturnsToIgnore(label);
   }

   /**
    * Returns the method {@link Node}s of method calls for
    * which its return should be ignored. If not already
    * available an empty method {@link Set} is created.
    * @param label The {@link SymbolicExecutionTermLabel} which provides the ID.
    * @return The {@link Set} of {@link Node}s to ignore its return.
    */
   protected Set<Node> getMethodReturnsToIgnore(SymbolicExecutionTermLabel label) {
      assert label != null : "No symbolic execuion term label provided";
      return getMethodReturnsToIgnore(label.getId());
   }
   
   /**
    * Returns the method {@link Node}s of method calls for
    * which its return should be ignored. If not already
    * available an empty method {@link Set} is created.
    * @param id The ID.
    * @return The {@link Set} of {@link Node}s to ignore its return.
    */
   protected Set<Node> getMethodReturnsToIgnore(int id) {
      synchronized (methodReturnsToIgnoreMap) {
         Integer key = Integer.valueOf(id);
         Set<Node> result = methodReturnsToIgnoreMap.get(key);
         if (result == null) {
            result = new LinkedHashSet<Node>();
            methodReturnsToIgnoreMap.put(key, result);
         }
         return result;
      }
   }

   /**
    * Returns the method call stack. If not already
    * available an empty method call stack is created.
    * @param ruleApp The {@link RuleApp} which modifies a modality {@link Term} with a {@link SymbolicExecutionTermLabel}.
    * @return The method call stack of the ID of the modified modality {@link Term} with a {@link SymbolicExecutionTermLabel}.
    */
   protected Map<Node, ImmutableList<Node>> getMethodCallStack(RuleApp ruleApp) {
      SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(ruleApp);
      return getMethodCallStack(label);
   }

   /**
    * Returns the method call stack. If not already
    * available an empty method call stack is created.
    * @param label The {@link SymbolicExecutionTermLabel} which provides the ID.
    * @return The method call stack of the ID of the given {@link SymbolicExecutionTermLabel}.
    */
   protected Map<Node, ImmutableList<Node>> getMethodCallStack(SymbolicExecutionTermLabel label) {
      assert label != null : "No symbolic execuion term label provided";
      return getMethodCallStack(label.getId());
   }

   /**
    * Returns the method call stack used for the given ID. If not already
    * available an empty method call stack is created.
    * @param id The ID.
    * @return The method call stack of the given ID.
    */
   protected Map<Node, ImmutableList<Node>> getMethodCallStack(int id) {
      synchronized (methodCallStackMap) {
         Integer key = Integer.valueOf(id);
         Map<Node, ImmutableList<Node>> result = methodCallStackMap.get(key);
         if (result == null) {
            result = new HashMap<Node, ImmutableList<Node>>();
            methodCallStackMap.put(key, result);
         }
         return result;
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
      if (methodCallStackMap != null) {
         methodCallStackMap.clear();
         methodCallStackMap = null;
      }
      if (afterBlockMap != null) {
         afterBlockMap.clear();
         afterBlockMap = null;
      }
      if (methodReturnsToIgnoreMap != null) {
         methodReturnsToIgnoreMap.clear();
         methodReturnsToIgnoreMap = null;
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
   public IExecutionStart getStartNode() {
      return startNode;
   }

   /**
    * This method must be called programmatically to update the
    * symbolic execution tree. The first call will create the initial tree
    * and further call will update the existing tree.
    * @return The detected {@link SymbolicExecutionCompletions} during symbolic execution.
    */
   public SymbolicExecutionCompletions analyse() {
      SymbolicExecutionCompletions completions = new SymbolicExecutionCompletions();
      AnalyzerProofVisitor visitor = new AnalyzerProofVisitor(completions);
      NodePreorderIterator iter = new NodePreorderIterator(proof.root());
      while (iter.hasNext()) {
         visitor.visit(proof, iter.next()); // This visitor pattern must be used because a recursive iteration causes StackOverflowErrors if the proof tree in KeY is to deep (e.g. simple list with 2000 elements during computation of fibonacci(7)
      }
      visitor.completeTree();
      return completions;
   }
   
   /**
    * Instances of this class are returned by {@link SymbolicExecutionTreeBuilder#analyse()}
    * to inform about newly completed blocks and returned methods.
    * @author Martin Hentschel
    */
   public static class SymbolicExecutionCompletions {
      /**
       * The newly block completion.
       */
      private final List<IExecutionNode<?>> blockCompletions = new LinkedList<IExecutionNode<?>>();

      /**
       * The newly methods return.
       */
      private final List<IExecutionBaseMethodReturn<?>> methodReturns = new LinkedList<IExecutionBaseMethodReturn<?>>();
      
      /**
       * Returns the newly block completion.
       * @return The newly block completion.
       */
      public IExecutionNode<?>[] getBlockCompletions() {
         return blockCompletions.toArray(new IExecutionNode<?>[blockCompletions.size()]);
      }
      
      /**
       * Registers the newly completed block.
       * @param blockCompletion The new block completion.
       */
      private void addBlockCompletion(IExecutionNode<?> blockCompletion) {
         if (blockCompletion != null) {
            blockCompletions.add(blockCompletion);
         }
      }
      
      /**
       * Returns the newly methods return.
       * @return The newly methods return.
       */
      public IExecutionBaseMethodReturn<?>[] getMethodReturns() {
         return methodReturns.toArray(new IExecutionBaseMethodReturn<?>[methodReturns.size()]);
      }
      
      /**
       * Registers the newly methods return.
       * @param methodReturn The method return.
       */
      private void addMethodReturn(IExecutionBaseMethodReturn<?> methodReturn) {
         if (methodReturn != null) {
            methodReturns.add(methodReturn);
         }
      }
   }
   
   /**
    * This {@link ProofVisitor} is used to transfer the proof tree in KeY
    * into {@link IExecutionNode}s which forms the symbolic execution tree.
    * @author Martin Hentschel
    */
   private class AnalyzerProofVisitor implements ProofVisitor {
      /**
       * The {@link SymbolicExecutionCompletions} to update.
       */
      private final SymbolicExecutionCompletions completions;
      
      /**
       * Maps the {@link Node} in KeY's proof tree to the {@link IExecutionNode} of the symbolic execution tree where the {@link Node}s children should be added to.
       */
      private Map<Node, AbstractExecutionNode<?>> addToMapping = new LinkedHashMap<Node, AbstractExecutionNode<?>>();

      /**
       * This utility {@link Map} helps to find a {@link List} in {@link #branchConditionsStack}
       * for the given parent node to that elements in the {@link List} should be added.
       */
      private Map<AbstractExecutionNode<?>, List<ExecutionBranchCondition>> parentToBranchConditionMapping = new LinkedHashMap<AbstractExecutionNode<?>, List<ExecutionBranchCondition>>();

      /**
       * Constructor.
       * @param completions The {@link SymbolicExecutionCompletions} to update.
       */
      public AnalyzerProofVisitor(SymbolicExecutionCompletions completions) {
         this.completions = completions;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(Proof proof, Node visitedNode) {
         // Find the parent node (IExecutionNode) to that the execution tree model representation of the given KeY's proof tree node should be added.
         AbstractExecutionNode<?> parentToAddTo = keyNodeBranchConditionMapping.get(visitedNode);
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
         parentToAddTo = analyzeNode(visitedNode, parentToAddTo, completions);
         addToMapping.put(visitedNode, parentToAddTo);
         // Check if the current node has branch conditions which should be added to the execution tree model
         if (!(parentToAddTo instanceof IExecutionStart) && // Ignore branch conditions before starting with code execution
             hasBranchCondition(visitedNode)) {
             Iterator<Node> iter = visitedNode.childrenIterator();
            while (iter.hasNext()) {
               Node childNode = iter.next();
               if (!keyNodeBranchConditionMapping.containsKey(childNode)) {
                  if (!shouldPrune(visitedNode)) { // Filter out branches that are closed
                     // Create branch condition
                     String additionalBranchLabel = null;
                     if (visitedNode.getAppliedRuleApp().rule() instanceof BuiltInRule) {
                        additionalBranchLabel = childNode.getNodeInfo().getBranchLabel();
                     }
                     ExecutionBranchCondition condition = new ExecutionBranchCondition(settings, childNode, additionalBranchLabel);
                     // Add branch condition to the branch condition attributes for later adding to the proof tree. This is required for instance to filter out branches after the symbolic execution has finished.
                     List<ExecutionBranchCondition> list = parentToBranchConditionMapping.get(parentToAddTo);
                     if (list == null) {
                        list = new LinkedList<ExecutionBranchCondition>();
                        branchConditionsStack.addFirst(new DefaultEntry<AbstractExecutionNode<?>, List<ExecutionBranchCondition>>(parentToAddTo, list));
                        parentToBranchConditionMapping.put(parentToAddTo, list);
                     }
                     list.add(condition);
                     keyNodeBranchConditionMapping.put(childNode, condition);
                     // Set call stack on new created node if possible
                     if (SymbolicExecutionUtil.hasSymbolicExecutionLabel(visitedNode.getAppliedRuleApp())) {
                        condition.setCallStack(createCallStack(visitedNode));
                     }
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
         Iterator<Entry<AbstractExecutionNode<?>, List<ExecutionBranchCondition>>> stackIter = branchConditionsStack.iterator();
         while (stackIter.hasNext()) {
            Entry<AbstractExecutionNode<?>, List<ExecutionBranchCondition>> entry = stackIter.next();
            Iterator<ExecutionBranchCondition> bcIter = entry.getValue().iterator();
            while (bcIter.hasNext()) {
               ExecutionBranchCondition condition = bcIter.next();
               AbstractExecutionNode<?>[] conditionsChildren = condition.getChildren(); 
               if (!ArrayUtil.isEmpty(conditionsChildren)) {
                  if (settings.isMergeBranchConditions()) {
                     // Merge branch conditions if possible
                     boolean addingToParentRequired = false;
                     for (AbstractExecutionNode<?> child : conditionsChildren) {
                        if (child instanceof ExecutionBranchCondition) {
                           ExecutionBranchCondition bcChild = (ExecutionBranchCondition)child;
                           bcChild.addMergedProofNode(condition.getProofNode());
                           addChild(entry.getKey(), child); // Move child one up in hierarchy
                           finishBlockCompletion(condition);
                        }
                        else {
                           addingToParentRequired = true; // Adding of current branch condition is required because non branch condition children are available
                        }
                     }
                     if (addingToParentRequired) {
                        addChild(entry.getKey(), condition);
                        finishBlockCompletion(condition);
                     }
                  }
                  else {
                     // Add all branch conditions without merging
                     addChild(entry.getKey(), condition);
                     finishBlockCompletion(condition);
                  }
                  bcIter.remove();
               }
            }
            if (entry.getValue().isEmpty()) {
               stackIter.remove();
            }
         }
      }
      
      protected void finishBlockCompletion(IExecutionBranchCondition node) {
         for (IExecutionBlockStartNode<?> start : node.getCompletedBlocks()) {
            ((AbstractExecutionBlockStartNode<?>) start).addBlockCompletion(node); // BranchConditions are updated when they are added to the SET.
            completions.addBlockCompletion(node);
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
    * @param completions The {@link SymbolicExecutionCompletions} to update.
    * @return The {@link IExecutionNode} to which children of the current {@link Node} should be added. If no execution tree model representation was created the return value is identical to the given one (parentToAddTo).
    */
   protected AbstractExecutionNode<?> analyzeNode(Node node, 
                                                  AbstractExecutionNode<?> parentToAddTo, 
                                                  SymbolicExecutionCompletions completions) {
      // Analyze node
      if (!shouldPrune(node)) { // Prune closed branches because they are invalid
         // Get required information
         NodeInfo info = node.getNodeInfo();
         SourceElement statement = info.getActiveStatement();
         // Update call stack
         updateCallStack(node, statement);
         // Update block map
         RuleApp currentOrFutureRuleApplication = node.getAppliedRuleApp();
         if (currentOrFutureRuleApplication == null && 
             node != proof.root()) { // Executing peekNext() on the root crashes the tests for unknown reasons.
            Goal goal = proof.getGoal(node);
            if (goal != null) {
               currentOrFutureRuleApplication = goal.getRuleAppManager().peekNext();
            }
         }
         if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, currentOrFutureRuleApplication)) {
            Map<JavaPair, ImmutableList<IExecutionNode<?>>> completedBlocks = updateAfterBlockMap(node, currentOrFutureRuleApplication);
            if (completedBlocks != null) {
               for (Entry<JavaPair, ImmutableList<IExecutionNode<?>>> entry : completedBlocks.entrySet()) {
                  for (IExecutionNode<?> entryNode : entry.getValue()) {
                     if (entryNode != parentToAddTo) { // Ignore empty blocks
                        if (entryNode instanceof AbstractExecutionBlockStartNode<?>) {
                           parentToAddTo.addCompletedBlock((AbstractExecutionBlockStartNode<?>) entryNode);
                           if (!(parentToAddTo instanceof IExecutionBranchCondition)) {
                              ((AbstractExecutionBlockStartNode<?>) entryNode).addBlockCompletion(parentToAddTo); // BranchConditions are updated when they are added to the SET.
                              completions.addBlockCompletion(parentToAddTo);
                           }
                        }
                     }
                  }
               }
            }
         }
         // Check if the node is already contained in the symbolic execution tree
         AbstractExecutionNode<?> executionNode = keyNodeMapping.get(node);
         if (executionNode == null) {
            // Try to create a new node
            executionNode = createExecutionTreeModelRepresentation(parentToAddTo, node, statement);
            parentToAddTo = addNodeToTreeAndUpdateParent(node, parentToAddTo, executionNode);
            // Check if execution node is a method return
            executionNode = createMehtodReturn(parentToAddTo, node, statement, completions);
            parentToAddTo = addNodeToTreeAndUpdateParent(node, parentToAddTo, executionNode);
         }
         else {
            parentToAddTo = executionNode;
         }
         // Check if loop condition is available
         boolean isLoopCondition = false;
         if (SymbolicExecutionUtil.hasLoopCondition(node, node.getAppliedRuleApp(), statement)) {
            if (((LoopStatement) statement).getGuardExpression().getPositionInfo() != PositionInfo.UNDEFINED &&
                !SymbolicExecutionUtil.isDoWhileLoopCondition(node, statement) && 
                !SymbolicExecutionUtil.isForLoopCondition(node, statement)) { // do while and for loops exists only in the first iteration where the loop condition is not evaluated. They are transfered into while loops in later proof nodes. 
               isLoopCondition = true;
            }
         }
         // Check if loop condition is available after loop invariant (rewritten into if statement)
         if (statement instanceof If && 
             ((If) statement).getExpression().getPositionInfo() != PositionInfo.UNDEFINED && 
             SymbolicExecutionUtil.getSymbolicExecutionLabel(node.getAppliedRuleApp()) != null &&
             searchDirectParentBodyPreservesInvariantBranchCondition(parentToAddTo) != null) {
            isLoopCondition = true;
         }
         // Create loop condition if required
         if (isLoopCondition) {
            ExecutionLoopCondition condition = keyNodeLoopConditionMapping.get(node);
            if (condition == null) {
               condition = new ExecutionLoopCondition(settings, node);
               addChild(parentToAddTo, condition);
               keyNodeLoopConditionMapping.put(node, condition);
               // Set call stack on new created node
               condition.setCallStack(createCallStack(node));
               Pair<Integer, SourceElement> secondPair = SymbolicExecutionUtil.computeSecondStatement(node.getAppliedRuleApp());
               addToBlockMap(node, condition, secondPair.first, secondPair.second, statement);
            }
            parentToAddTo = condition;
         }
      }
      return parentToAddTo;
   }
   
   /**
    * Searches the direct parent {@link IExecutionBranchCondition} representing
    * the 'Body Preserves Invariant' branch.
    * @param current The {@link IExecutionNode} to check its parent {@link IExecutionBranchCondition}s.
    * @return The found {@link IExecutionBranchCondition} or {@code null} if not available.
    */
   protected IExecutionBranchCondition searchDirectParentBodyPreservesInvariantBranchCondition(IExecutionNode<?> current) {
      Iterator<Entry<AbstractExecutionNode<?>, List<ExecutionBranchCondition>>> iter = branchConditionsStack.iterator();
      while (current instanceof IExecutionBranchCondition) {
         if (WhileInvariantRule.BODY_PRESERVES_INVARIANT_LABEL.equals(current.getProofNode().getNodeInfo().getBranchLabel())) {
            return (IExecutionBranchCondition) current;
         }
         else {
            // Search parent (current.getParent() is not yet defined)
            boolean parentFound = false;
            while (!parentFound && iter.hasNext()) {
               Entry<AbstractExecutionNode<?>, List<ExecutionBranchCondition>> entry = iter.next();
               if (entry.getValue().contains(current)) {
                  current = entry.getKey();
                  parentFound = true;
               }
            }
            if (!parentFound) {
               current = null;
            }
         }
      }
      return null;
   }

   protected boolean shouldPrune(Node node) {
      if (isUninterpretedPredicateUsed) {
         return node.isClosed();
      }
      else {
         return false;
      }
   }
   
   /**
    * Adds the new created {@link AbstractExecutionNode} to the symbolic execution tree
    * if available and returns the new parent for future detected nodes.
    * @param node The {@link Node}.
    * @param parentToAddTo The parent {@link AbstractExecutionNode}.
    * @param executionNode The new child {@link AbstractExecutionNode}.
    * @return The new parent {@link AbstractExecutionNode}.
    */
   protected AbstractExecutionNode<?> addNodeToTreeAndUpdateParent(Node node, 
                                                                   AbstractExecutionNode<?> parentToAddTo, 
                                                                   AbstractExecutionNode<?> executionNode) {
      // Check if a new node was created
      if (executionNode != null) {
         // Add new node to symbolic execution tree
         addChild(parentToAddTo, executionNode);
         keyNodeMapping.put(node, executionNode);
         parentToAddTo = executionNode;
         // Set call stack on new created node
         executionNode.setCallStack(createCallStack(node));
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
      SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(node.getAppliedRuleApp());
      if (label != null && 
          SymbolicExecutionUtil.isMethodCallNode(node, node.getAppliedRuleApp(), statement, true)) {
         // Remove outdated methods from call stack
         int currentLevel = SymbolicExecutionUtil.computeStackSize(node.getAppliedRuleApp());
         Map<Node, ImmutableList<Node>> methodCallStack = getMethodCallStack(label);
         ImmutableList<Node> stack = findMethodCallStack(methodCallStack, node);
         if (stack != null) {
            while (stack.size() > currentLevel) {
               stack = stack.take(1);
            }
         }
         else {
            stack = ImmutableSLList.nil();
         }
         // Add new node to call stack.
         stack = stack.prepend(node);
         methodCallStack.put(node, stack);
      }
   }
   
   protected ImmutableList<Node> findMethodCallStack(Map<Node, ImmutableList<Node>> methodCallStack, Node node) {
      ImmutableList<Node> result = null;
      while (result == null && node != null) {
         result = methodCallStack.get(node);
         node = node.parent();
      }
      return result;
   }

   /**
    * Creates a new execution tree model representation ({@link IExecutionNode}) 
    * if possible for the given {@link Node} in KeY's proof tree.
    * @param parent The parent {@link IExecutionNode}.
    * @param node The {@link Node} in the proof tree of KeY.
    * @param statement The actual statement ({@link SourceElement}).
    * @return The created {@link IExecutionNode} or {@code null} if the {@link Node} should be ignored in the symbolic execution tree.
    */
   protected AbstractExecutionNode<?> createExecutionTreeModelRepresentation(AbstractExecutionNode<?> parent,
                                                                             Node node, 
                                                                             SourceElement statement) {
      AbstractExecutionNode<?> result = null;
      // Make sure that a statement (SourceElement) is available.
      if (SymbolicExecutionUtil.hasSymbolicExecutionLabel(node.getAppliedRuleApp())) {
         if (statement != null && !SymbolicExecutionUtil.isRuleAppToIgnore(node.getAppliedRuleApp())) {
            // Get position information
            PositionInfo posInfo = statement.getPositionInfo();
            // Determine the node representation and create it if one is available
            if (SymbolicExecutionUtil.isMethodCallNode(node, node.getAppliedRuleApp(), statement)) {
               result = new ExecutionMethodCall(settings, node);
            }
            else if (SymbolicExecutionUtil.isTerminationNode(node, node.getAppliedRuleApp())) {
               if (!SymbolicExecutionUtil.hasLoopBodyLabel(node.getAppliedRuleApp())) {
                  result = new ExecutionTermination(settings, node, exceptionVariable, null);
                  startNode.addTermination((ExecutionTermination)result);
               }
            }
            else if (SymbolicExecutionUtil.isBranchStatement(node, node.getAppliedRuleApp(), statement, posInfo)) {
               if (isNotInImplicitMethod(node)) {
                  result = new ExecutionBranchStatement(settings, node);
                  addToBlockMap(node, (ExecutionBranchStatement)result);
               }
            }
            else if (SymbolicExecutionUtil.isLoopStatement(node, node.getAppliedRuleApp(), statement, posInfo)) {
               if (isNotInImplicitMethod(node)) {
                  result = new ExecutionLoopStatement(settings, node);
                  addToBlockMap(node, (ExecutionLoopStatement)result);
               }
            }
            else if (SymbolicExecutionUtil.isStatementNode(node, node.getAppliedRuleApp(), statement, posInfo)) {
               if (isNotInImplicitMethod(node)) {
                  result = new ExecutionStatement(settings, node);
               }
            }
         }
         else if (SymbolicExecutionUtil.isOperationContract(node, node.getAppliedRuleApp())) {
            if (isNotInImplicitMethod(node)) {
               result = new ExecutionOperationContract(settings, node);
            }
         }
         else if (SymbolicExecutionUtil.isLoopInvariant(node, node.getAppliedRuleApp())) {
            if (isNotInImplicitMethod(node)) {
               result = new ExecutionLoopInvariant(settings, node);
               // Initialize new call stack of the preserves loop invariant branch
               initNewLoopBodyMethodCallStack(node);
            }
         }
      }
      else if (SymbolicExecutionUtil.isLoopBodyTermination(node, node.getAppliedRuleApp())) {
         result = new ExecutionTermination(settings, node, exceptionVariable, TerminationKind.LOOP_BODY);
         startNode.addTermination((ExecutionTermination)result);
      }
      return result;
   }
   
   /**
    * Adds the given {@link AbstractExecutionNode} add reason for a new block to the block maps.
    * @param node The current {@link Node}.
    * @param blockStartNode The {@link AbstractExecutionNode} to add.
    */
   protected void addToBlockMap(Node node, AbstractExecutionBlockStartNode<?> blockStartNode) {
      Pair<Integer, SourceElement> secondPair = SymbolicExecutionUtil.computeSecondStatement(node.getAppliedRuleApp());
      addToBlockMap(node, blockStartNode, secondPair.first, secondPair.second);
   }
   
   /**
    * Adds the given {@link AbstractExecutionNode} add reason for a new block to the block maps.
    * @param node The current {@link Node}.
    * @param blockStartNode The {@link AbstractExecutionNode} to add.
    * @param secondPair The next element to end at.
    * @return {@code false} block is definitively not opened, {@code true} block is or might be opened.
    */
   protected void addToBlockMap(Node node, AbstractExecutionBlockStartNode<?> blockStartNode, int stackSize, SourceElement... sourceElements) {
      boolean blockPossible = checkBlockPossibility(node, stackSize, sourceElements);
      if (blockPossible) {
         if (sourceElements != null && sourceElements.length >= 1) {
            SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(node.getAppliedRuleApp());
            // Find most recent map
            Map<Node, Map<JavaPair, ImmutableList<IExecutionNode<?>>>> afterBlockMaps = getAfterBlockMaps(label);
            Map<JavaPair, ImmutableList<IExecutionNode<?>>> afterBlockMap = findAfterBlockMap(afterBlockMaps, node);
            if (afterBlockMap == null) {
               afterBlockMap = new LinkedHashMap<JavaPair, ImmutableList<IExecutionNode<?>>>();
            }
            else {
               afterBlockMap = new LinkedHashMap<JavaPair, ImmutableList<IExecutionNode<?>>>(afterBlockMap);
            }
            afterBlockMaps.put(node, afterBlockMap);
            JavaPair secondPair = new JavaPair(stackSize, ImmutableSLList.<SourceElement>nil().append(sourceElements));
            ImmutableList<IExecutionNode<?>> blockStartList = afterBlockMap.get(secondPair);
            if (blockStartList == null) {
               blockStartList = ImmutableSLList.nil();
            }
            blockStartList = blockStartList.append(blockStartNode);
            afterBlockMap.put(secondPair, blockStartList);
         }
      }
      blockStartNode.setBlockOpened(blockPossible);
   }
   
   /**
    * Checks if it possible that the current {@link Node} opens a block.
    * @param node The current {@link Node}.
    * @param expectedStackSize The expected stack size.
    * @param expectedSourceElements The expected after block {@link SourceElement}s.
    * @return {@code false} A block is definitively not possible, {@code true} a block is or might be possible. 
    */
   private boolean checkBlockPossibility(Node node, 
                                         int expectedStackSize, 
                                         SourceElement... expectedSourceElements) {
      if (node != null && expectedSourceElements != null && expectedSourceElements.length >= 1) {
         RuleApp ruleApp = null;
         boolean seNodeFound = false;
         // Find single symbolic execution child node
         while (!seNodeFound && node != null) {
            // Select new child node
            if (node.childrenCount() > 1) {
               int i = 0;
               int openChildCount = 0;
               Node nextNode = null;
               while (i < node.childrenCount()) {
                  Node child = node.child(i);
                  if (!child.isClosed()) {
                     openChildCount++;
                     nextNode = child;
                  }
                  i++;
               }
               if (openChildCount == 1) {
                  node = nextNode;
               }
               else {
                  node = null; // Stop search because multiple open branches indicate that a block is required.
               }
            }
            else if (node.childrenCount() == 1) {
               node = node.child(0);
            }
            else {
               node = null;
            }
            // Check selected child
            if (node != null) {
               if (node.childrenCount() == 0) {
                  Goal goal = proof.getGoal(node);
                  ruleApp = goal.getRuleAppManager().peekNext();
               }
               else {
                  ruleApp = node.getAppliedRuleApp();
               }
               seNodeFound = SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp);
            }
         }
         // If SE node is found check if the after block state is reached.
         if (seNodeFound) {
            int currentStackSize = SymbolicExecutionUtil.computeStackSize(ruleApp);
            SourceElement currentActiveStatement = NodeInfo.computeActiveStatement(ruleApp);
            JavaBlock currentJavaBlock = ruleApp.posInOccurrence().subTerm().javaBlock();
            MethodFrame currentInnerMostMethodFrame = JavaTools.getInnermostMethodFrame(currentJavaBlock, proof.getServices());
            return !isAfterBlockReached(currentStackSize, currentInnerMostMethodFrame, currentActiveStatement, expectedStackSize, ImmutableSLList.<SourceElement>nil().append(expectedSourceElements).iterator());
         }
         else {
            return true; // No single SE node reached, so allow blocks
         }
      }
      else {
         return true; // Don't know, so allow blocks
      }
   }
   
   /**
    * Searches the relevant after block {@link Map} in the given once for the given {@link Node}.
    * @param afterBlockMaps The available after sblock {@link Map}s.
    * @param node The {@link Node} for which the block {@link Map} is requested.
    * @return The found after block {@link Map} or {@code null} if not available.
    */
   protected Map<JavaPair, ImmutableList<IExecutionNode<?>>> findAfterBlockMap(Map<Node, Map<JavaPair, ImmutableList<IExecutionNode<?>>>> afterBlockMaps, Node node) {
      if (afterBlockMaps != null) {
         Map<JavaPair, ImmutableList<IExecutionNode<?>>> result = null;
         while (result == null && node != null) {
            result = afterBlockMaps.get(node);
            node = node.parent();
         }
         return result;
      }
      else {
         return null;
      }
   }

   /**
    * Returns the after block map. If not already
    * available an empty block map is created.
    * @param label The {@link SymbolicExecutionTermLabel} which provides the ID.
    * @return The after block map of the ID of the given {@link SymbolicExecutionTermLabel}.
    */
   protected Map<Node, Map<JavaPair, ImmutableList<IExecutionNode<?>>>> getAfterBlockMaps(SymbolicExecutionTermLabel label) {
      assert label != null : "No symbolic execuion term label provided";
      return getAfterBlockMaps(label.getId());
   }

   /**
    * Returns the after block map used for the given ID. If not already
    * available an empty block map is created.
    * @param id The ID.
    * @return The after block map of the given ID.
    */
   protected Map<Node, Map<JavaPair, ImmutableList<IExecutionNode<?>>>> getAfterBlockMaps(int id) {
      synchronized (afterBlockMap) {
         Integer key = Integer.valueOf(id);
         Map<Node, Map<JavaPair, ImmutableList<IExecutionNode<?>>>> result = afterBlockMap.get(key);
         if (result == null) {
            result = new LinkedHashMap<Node, Map<JavaPair, ImmutableList<IExecutionNode<?>>>>();
            afterBlockMap.put(key, result);
         }
         return result;
      }
   }
   
   /**
    * Updates the after block maps when a symbolic execution tree node is detected.
    * @param node The {@link Node} which is a symbolic execution tree node.
    * @param ruleApp The {@link RuleApp} to consider.
    * @return The now completed blocks.
    */
   protected Map<JavaPair, ImmutableList<IExecutionNode<?>>> updateAfterBlockMap(Node node, RuleApp ruleApp) {
      Map<JavaPair, ImmutableList<IExecutionNode<?>>> completedBlocks = new LinkedHashMap<JavaPair, ImmutableList<IExecutionNode<?>>>();
      SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(ruleApp);
      if (label != null) {
         // Find most recent map
         Map<Node, Map<JavaPair, ImmutableList<IExecutionNode<?>>>> afterBlockMaps = getAfterBlockMaps(label);
         Map<JavaPair, ImmutableList<IExecutionNode<?>>> oldBlockMap = findAfterBlockMap(afterBlockMaps, node);
         if (oldBlockMap != null) {
            // Compute stack and active statement
            int stackSize = SymbolicExecutionUtil.computeStackSize(ruleApp);
            SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
            JavaBlock javaBlock = ruleApp.posInOccurrence().subTerm().javaBlock();
            MethodFrame innerMostMethodFrame = JavaTools.getInnermostMethodFrame(javaBlock, proof.getServices());
            // Create copy with values below level
            Map<JavaPair, ImmutableList<IExecutionNode<?>>> newBlockMap = new LinkedHashMap<JavaPair, ImmutableList<IExecutionNode<?>>>();
            if (oldBlockMap != null) {
               for (Entry<JavaPair, ImmutableList<IExecutionNode<?>>> entry : oldBlockMap.entrySet()) {
                  if (!isContained(entry.getValue(), node)) { // Ensure that with stepwise execution loops are not completed by their own.
                     boolean done = isAfterBlockReached(stackSize, innerMostMethodFrame, activeStatement, entry.getKey());
                     if (done) {
                        completedBlocks.put(entry.getKey(), entry.getValue());
                     }
                     else {
                        newBlockMap.put(entry.getKey(), entry.getValue());
                     }
                  }
               }
            }
            // Add new block
            afterBlockMaps.put(node, newBlockMap);
         }
      }
      return completedBlocks;
   }
   
   /**
    * Checks if one of the give {@link IExecutionNode}s represents the given {@link Node}.
    * @param list The {@link IExecutionNode}s to check.
    * @param node The {@link Node} to check for.
    * @return {@code true} is contained, {@code false} is not contained.
    */
   protected boolean isContained(ImmutableList<IExecutionNode<?>> list, Node node) {
      boolean contained = false;
      Iterator<IExecutionNode<?>> iter = list.iterator();
      while (!contained && iter.hasNext()) {
         IExecutionNode<?> next = iter.next();
         if (next.getProofNode() == node) {
            contained = true;
         }
      }
      return contained;
   }

   /**
    * Checks if the after block condition is fulfilled.
    * @param currentStackSize The current stack size.
    * @param currentInnerMostMethodFrame The current inner most {@link MethodFrame}.
    * @param currentActiveStatement The current active statement.
    * @param expectedPair The {@link JavaPair} specifying the after block statements.
    * @return {@code true} after block is reached, {@code false} after block is not reached.
    */
   protected boolean isAfterBlockReached(int currentStackSize, 
                                         MethodFrame currentInnerMostMethodFrame, 
                                         SourceElement currentActiveStatement, 
                                         JavaPair expectedPair) {
      return isAfterBlockReached(currentStackSize, currentInnerMostMethodFrame, currentActiveStatement, expectedPair.first, expectedPair.second.iterator());
   }
   
   /**
    * Checks if the after block condition is fulfilled.
    * @param currentStackSize The current stack size.
    * @param currentInnerMostMethodFrame The current inner most {@link MethodFrame}.
    * @param currentActiveStatement The current active statement.
    * @param expectedStackSize The expected stack size.
    * @param expectedStatementsIterator An {@link Iterator} with the expected after block statements.
    * @return {@code true} after block is reached, {@code false} after block is not reached.
    */
   protected boolean isAfterBlockReached(int currentStackSize, 
                                         MethodFrame currentInnerMostMethodFrame, 
                                         SourceElement currentActiveStatement, 
                                         int expectedStackSize,
                                         Iterator<SourceElement> expectedStatementsIterator) {
      boolean done = false;
      if (expectedStackSize > currentStackSize) {
         done = true;
      }
      else {
         while (!done && expectedStatementsIterator.hasNext()) {
            SourceElement next = expectedStatementsIterator.next();
            if (SymbolicExecutionUtil.equalsWithPosition(next, currentActiveStatement)) { // Comparison by == is not possible since loops are recreated
               done = true;
            }
            else if (expectedStackSize == currentStackSize &&
                     (currentInnerMostMethodFrame != null && currentInnerMostMethodFrame.getBody().isEmpty() ||
                      (next != null && !SymbolicExecutionUtil.containsStatement(currentInnerMostMethodFrame, next, proof.getServices())))) {
               done = true;
            }
         }
      }
      return done;
   }
   
   /**
    * Creates an method return node.
    * @param parent The parent {@link AbstractExecutionNode}.
    * @param node The {@link Node} which represents a method return.
    * @param statement The currently active {@link SourceElement}.
    * @param completions The {@link SymbolicExecutionCompletions} to update.
    * @return The created {@link AbstractExecutionMethodReturn}.
    */
   protected AbstractExecutionMethodReturn<?> createMehtodReturn(AbstractExecutionNode<?> parent,
                                                                 Node node, 
                                                                 SourceElement statement,
                                                                 SymbolicExecutionCompletions completions) {
      AbstractExecutionMethodReturn<?> result = null;
      if (SymbolicExecutionUtil.hasSymbolicExecutionLabel(node.getAppliedRuleApp())) {
         if (statement != null && !SymbolicExecutionUtil.isRuleAppToIgnore(node.getAppliedRuleApp())) {
            boolean methodReturn = SymbolicExecutionUtil.isMethodReturnNode(node, node.getAppliedRuleApp());
            boolean exceptionalMethodReturn = !methodReturn && SymbolicExecutionUtil.isExceptionalMethodReturnNode(node, node.getAppliedRuleApp());
            if (methodReturn || exceptionalMethodReturn) {
               // Find the Node in the proof tree of KeY for that this Node is the return
               Node callNode = findMethodCallNode(node, node.getAppliedRuleApp());
               if (callNode != null) {
                  // Make sure that the return should not be ignored
                  Set<Node> methodReturnsToIgnore = getMethodReturnsToIgnore(node.getAppliedRuleApp()); 
                  if (!methodReturnsToIgnore.contains(callNode)) {
                     // Find the call Node representation in SED, if not available ignore it.
                     IExecutionNode<?> callSEDNode = keyNodeMapping.get(callNode);
                     if (callSEDNode instanceof ExecutionMethodCall) { // Could be the start node if the initial sequent already contains some method frames.
                        if (methodReturn) {
                           result = new ExecutionMethodReturn(settings, node, (ExecutionMethodCall)callSEDNode);
                           completions.addMethodReturn(result);
                        }
                        else {
                           result = new ExecutionExceptionalMethodReturn(settings, node, (ExecutionMethodCall)callSEDNode);
                           completions.addMethodReturn(result);
                        }
                     }
                  }
               }
            }
         }
      }
      return result;
   }
   
   /**
    * Checks if the given {@link Node} is not in an implicit method.
    * @param node The {@link Node} to check.
    * @return {@code true} is not implicit, {@code false} is implicit 
    */
   protected boolean isNotInImplicitMethod(Node node) {
      Term term = node.getAppliedRuleApp().posInOccurrence().subTerm();
      term = TermBuilder.goBelowUpdates(term);
      Services services = proof.getServices();
      IExecutionContext ec = JavaTools.getInnermostExecutionContext(term.javaBlock(), services);
      IProgramMethod pm = ec.getMethodContext();
      return SymbolicExecutionUtil.isNotImplicit(services, pm);
   }
   
   /**
    * This method initializes the method call stack of loop body modalities
    * with the values from the original call stack. For each {@link MethodFrame}
    * in the new modality is its method call {@link Node} added to the new
    * method call stack.
    * @param node The {@link Node} on which the loop invariant rule is applied.
    */
   protected void initNewLoopBodyMethodCallStack(Node node) {
      PosInOccurrence newModalityPIO = SymbolicExecutionUtil.findModalityWithMaxSymbolicExecutionLabelId(node.child(1).sequent());
      Term newModality = newModalityPIO != null ? newModalityPIO.subTerm() : null;
      assert newModality != null;
      SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(newModality);
      assert label != null;
      JavaBlock jb = newModality.javaBlock();
      MethodFrameCounterJavaASTVisitor newCounter = new MethodFrameCounterJavaASTVisitor(jb.program(), proof.getServices());
      int newCount = newCounter.run();
      Term oldModality = node.getAppliedRuleApp().posInOccurrence().subTerm();
      oldModality = TermBuilder.goBelowUpdates(oldModality);
      Map<Node, ImmutableList<Node>> currentMethodCallStackMap = getMethodCallStack(node.getAppliedRuleApp());
      Map<Node, ImmutableList<Node>> newMethodCallStackMap = getMethodCallStack(label.getId());
      ImmutableList<Node> currentMethodCallStack = findMethodCallStack(currentMethodCallStackMap, node);
      ImmutableList<Node> newMethodCallStack = ImmutableSLList.nil();
      Set<Node> currentIgnoreSet = getMethodReturnsToIgnore(label.getId());
      assert newMethodCallStack.isEmpty() : "Method call stack is not empty.";
      currentMethodCallStack = currentMethodCallStack.take(currentMethodCallStack.size() - newCount);
      Iterator<Node> currentIter = currentMethodCallStack.iterator();
      while (currentIter.hasNext()) {
         Node next = currentIter.next();
         newMethodCallStack = newMethodCallStack.prepend(next);
         currentIgnoreSet.add(next);
      }
      newMethodCallStackMap.put(node, newMethodCallStack);
   }

   /**
    * Utility class used in {@link SymbolicExecutionTreeBuilder#initNewLoopBodyMethodCallStack(Node)}
    * to compute the number of available {@link MethodFrame}s.
    * @author Martin Hentschel
    */
   private static final class MethodFrameCounterJavaASTVisitor extends JavaASTVisitor {
      /**
       * The number of {@link MethodFrame}s.
       */
      private int count = 0;
      
      /**
       * Constructor.
       * @param root The {@link ProgramElement} to count the contained {@link MethodFrame}s.
       * @param services The {@link Services} to use.
       */
      public MethodFrameCounterJavaASTVisitor(ProgramElement root, Services services) {
         super(root, services);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void doDefaultAction(SourceElement node) {
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void performActionOnMethodFrame(MethodFrame x) {
         count++;
      }

      /**
       * Performs the counting of {@link MethodFrame}s.
       * @return The number of found {@link MethodFrame}s.
       */
      public int run() {
         walk(root());
         return count;
      }
   }
   
   /**
    * Computes the method call stack of the given {@link Node}.
    * @param node The {@link Node}.
    * @return The computed method call stack.
    */
   protected IExecutionNode<?>[] createCallStack(Node node) {
      // Compute number of call stack size
      int size = SymbolicExecutionUtil.computeStackSize(node.getAppliedRuleApp());
      if (size >= 1) {
         // Add call stack entries
         List<IExecutionNode<?>> callStack = new LinkedList<IExecutionNode<?>>();
         Map<Node, ImmutableList<Node>> methodCallStack = getMethodCallStack(node.getAppliedRuleApp());
         ImmutableList<Node> stack = findMethodCallStack(methodCallStack, node);
         stack = stack.take(stack.size() - size);
         Iterator<Node> stackIter = stack.iterator();
         for (int i = 0; i < size; i++) {
            Node stackEntry = stackIter.next();
            if (stackEntry != proof.root()) { // Ignore call stack entries provided by the initial sequent
               IExecutionNode<?> executionNode = getExecutionNode(stackEntry);
               assert executionNode != null : "Can't find execution node for KeY's proof node " + stackEntry.serialNr() + ": " + ProofSaver.printAnything(stackEntry, proof.getServices()) + ".";
               callStack.add(executionNode);
            }
         }
         return callStack.toArray(new IExecutionNode[callStack.size()]);
      }
      else {
         return new IExecutionNode[0];
      }
   }

   /**
    * Finds the {@link Node} in the proof tree of KeY which has called the
    * method that is now executed or returned in the {@link Node}.
    * @param currentNode The {@link Node} for that the method call {@link Node} is needed.
    * @return The found call {@link Node} or {@code null} if no one was found.
    */
   protected Node findMethodCallNode(Node currentNode, RuleApp ruleApp) {
      // Compute the stack frame size before the method is called
      int returnStackSize = SymbolicExecutionUtil.computeStackSize(ruleApp);
      // Return the method from the call stack
      if (returnStackSize >= 0) {
         Map<Node, ImmutableList<Node>> methodCallStack = getMethodCallStack(ruleApp);
         ImmutableList<Node> stack = findMethodCallStack(methodCallStack, currentNode);
         return stack.take(stack.size() - returnStackSize).head();
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
      if (node.childrenCount() >= 2) { // Check if it is a possible branch statement, otherwise there is no need for complex computation to filter out not relevant branches
         int openChildrenCount = 0;
         Iterator<Node> childIter = node.childrenIterator();
         while (childIter.hasNext()) {
            Node child = childIter.next();
            // Make sure that the branch is not closed
            if (!shouldPrune(child)) {
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
   protected void addChild(AbstractExecutionNode<?> parent, AbstractExecutionNode<?> child) {
      child.setParent(parent);
      parent.addChild(child);
   }

   /**
    * <p>
    * Searches the {@link IExecutionNode} which represents the given {@link Node} of KeY's proof tree.
    * <p>
    * In case that the {@link Node} is represented by multiple {@link AbstractExecutionNode}s,
    * e.g. a return statement and a method return, the last node is returned.
    * </p>
    * @param proofNode The {@link Node} in KeY's proof tree.
    * @return The {@link IExecutionNode} representation or {@code null} if no one is available.
    */
   public IExecutionNode<?> getExecutionNode(Node proofNode) {
      IExecutionNode<?> result = keyNodeMapping.get(proofNode);
      if (result == null) {
         result = keyNodeBranchConditionMapping.get(proofNode);
      }
      if (result == null) {
         result = keyNodeLoopConditionMapping.get(proofNode);
      }
      return result;
   }
   
   /**
    * Returns the minimal required PO {@link Properties} to support
    * symbolic execution tree extraction in a {@link SymbolicExecutionJavaProfile}.
    * @return The minimal required PO {@link Properties}.
    */
   public static Properties createPoPropertiesToForce() {
      Properties poPropertiesToForce = new Properties();
      poPropertiesToForce.setProperty(IPersistablePO.PROPERTY_ADD_SYMBOLIC_EXECUTION_LABEL, true + "");
      return poPropertiesToForce;
   }
   
   /**
    * Utility class to  group a call stack size with an {@link ImmutableList} of {@link SourceElement} with the elements of interest.
    * @author Martin Hentschel
    */
   protected static class JavaPair extends Pair<Integer, ImmutableList<SourceElement>> {
      /**
       * Constructor.
       * @param stackSize The call stack size.
       * @param elementsOfInterest The {@link SourceElement}s of interest.
       */
      public JavaPair(Integer stackSize, ImmutableList<SourceElement> elementsOfInterest) {
         super(stackSize, elementsOfInterest);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object o) {
         if (super.equals(o)) {
            if (o instanceof JavaPair) {
               JavaPair other = (JavaPair) o;
               if (second.size() == other.second.size()) {
                  Iterator<SourceElement> iter = second.iterator();
                  Iterator<SourceElement> otherIter = other.second.iterator();
                  boolean equals = true;
                  while (equals && iter.hasNext()) {
                     SourceElement next = iter.next();
                     SourceElement otherNext = otherIter.next();
                     if (!SymbolicExecutionUtil.equalsWithPosition(next, otherNext)) { // Comparison by == is not possible since loops are recreated
                        equals = false;
                     }
                  }
                  assert !otherIter.hasNext();
                  return equals;
               }
               else {
                  return false;
               }
            }
            else {
               return false;
            }
         }
         else {
            return false;
         }
      }
   }
}