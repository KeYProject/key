package org.key_project.sed.key.core.model;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.memory.ISEDMemoryStackFrameCompatibleDebugNode;
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEDMemoryBranchNode;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryTermination;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;

/**
 * Implementation if {@link ISEDDebugTarget} which uses KeY to symbolically
 * debug a program.
 * @author Martin Hentschel
 */
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
    * Maps the KeY instances to the debug API instances.
    */
   private Map<Node, ISEDDebugNode> keyNodeMapping;
   
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
      // Observe frozen state of KeY Main Frame
      MainWindow.getInstance().getMediator().addAutoModeListener(autoModeListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return super.canResume() && 
             !MainWindow.getInstance().frozen; // Only one proof completion per time is possible
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      if (canResume()) {
         // Inform UI that the process is resumed
         super.resume();
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
    * Analyzes the given Proof by printing the executed code in the console.
    * @param proof The Proof to analyze.
    * @throws DebugException Occurred Exception.
    */
   protected void analyzeProof(Proof proof) throws DebugException {
      analyzeNode(proof.root(), 0, thread);
   }

   /**
    * <p>
    * Analyzes the given Proof by printing the executed code in the console.
    * </p>
    * <p>
    * <b>Attention :</b> A correct pruning requires at the moment that
    * the Taclet Option "runtimeExceptions" is set to "runtimeExceptions:allow".
    * Alternatively it is required to modify rule {@code assignment_to_reference_array_component}
    * in file {@code javaRules.key} by uncommenting {@code \add (!(#v=null) & lt(#se, length(#v)) & geq(#se,0) & arrayStoreValid(#v, #se0)==>)}. 
    * </p>
    * @param proof The Proof to analyze.
    * @throws DebugException Occurred Exception.
    */
   protected void analyzeNode(Node node, int level, ISEDDebugNode parentToAddTo) throws DebugException {
      // Analyze node
      if (!node.isClosed()) { // Prune closed branches because they are invalid
         // Get required informations
         NodeInfo info = node.getNodeInfo();
         SourceElement statement = info.getActiveStatement();
         // Check if the node is already contained in the symbolic execution tree
         ISEDDebugNode debugNode = keyNodeMapping.get(node);
         if (debugNode == null) {
            // Try to create a new node
            debugNode = createNodeForStatement(node, info, statement);
            // Check if a new node was created
            if (debugNode != null) {
               // Add new node to symbolic execution tree
               addChild(parentToAddTo, debugNode);
               keyNodeMapping.put(node, debugNode);
               parentToAddTo = debugNode;
            }
         }
         // Iterate over children
         NodeIterator children = node.childrenIterator();
         while (children.hasNext()) {
            Node child = children.next();
            analyzeNode(child, level + 1, parentToAddTo);
         }
      }
   }
   
   /**
    * Creates a new {@link ISEDDebugNode} if possible for the given {@link Node}
    * in the proof tree.
    * @param node The {@link Node} in the proof tree of KeY.
    * @param info The {@link NodeInfo}.
    * @param statement The actual statement ({@link SourceElement}).
    * @return The created {@link ISEDDebugNode} or {@code null} if the {@link Node} should be ignored in the symbolic execution debugger (SED).
    * @throws DebugException Occurred Exception.
    */
   protected ISEDDebugNode createNodeForStatement(Node node, NodeInfo info, SourceElement statement) throws DebugException {
      ISEDDebugNode result = null;
      // Make sure that a statement (SourceElement) is available.
      if (statement != null) {
         // Get position information
         PositionInfo posInfo = statement.getPositionInfo();
         // Determine the node representation and create it if one is available
         if (isMethodCallNode(node, info, statement, posInfo)) {
            Assert.isTrue(statement instanceof MethodBodyStatement, "isMethodCallNode has to verify that the statement is an instance of MethodBodyStatement");
            MethodBodyStatement mbs = (MethodBodyStatement)statement;
            result = createMethodCallNode(mbs, posInfo);
         }
         else if (isMethodReturnNode(node, info, statement, posInfo)) {
            result = createMethodReturnNode(node, statement, posInfo);
         }
         else if (isTerminationNode(node, info, statement, posInfo)) {
            result = createTerminationNode(statement, posInfo);
         }
         else if (isStatementNode(node, info, statement, posInfo)) {
            result = createStatementNode(statement, posInfo);
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
    * Creates a new {@link ISEDTermination} for the given {@link SourceElement}.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDTermination}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDTermination}.
    */
   protected ISEDTermination createTerminationNode(SourceElement statement, PositionInfo posInfo) {
      // Compute method name
      String name = DEFAULT_TERMINATION_NODE_NAME;
      // Create new node and fill it
      SEDMemoryTermination newNode = new SEDMemoryTermination(getDebugTarget(), thread, thread);
      fillNode(newNode, name, posInfo);
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
    * Creates a new {@link ISEDMethodReturn} for the given {@link SourceElement}.
    * @param node The {@link Node} in the proof tree of KeY.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDStatement}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDMethodCall}.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDMethodReturn createMethodReturnNode(Node node, SourceElement statement, PositionInfo posInfo) throws DebugException {
      // Find the node with the method call which is now returned
      Node callNode = KeYUtil.findParent(node, new IFilter<Node>() {
         @Override
         public boolean select(Node element) {
            if (element != null) {
               NodeInfo info = element.getNodeInfo();
               SourceElement statement = info != null ? info.getActiveStatement() : null;
               PositionInfo posInfo = statement != null ? statement.getPositionInfo() : null;
               return isMethodCallNode(element, info, statement, posInfo);
            }
            else {
               return false;
            }
         }
      });
      Assert.isNotNull(callNode);
      ISEDDebugNode callSEDNode = keyNodeMapping.get(callNode);
      Assert.isTrue(callSEDNode instanceof ISEDMethodCall);
      // Find last return node
      Node returnNode = KeYUtil.findParent(node, new IFilter<Node>() {
         @Override
         public boolean select(Node element) {
            return "methodCallReturn".equals(KeYUtil.getRuleDisplayName(element));
         }
      });
      // Make sure that the return node is a child of the call node and not of a call earlier in the call stack
      if (!KeYUtil.hasParent(returnNode, callNode)) {
         returnNode = null;
      }
      // Compute return value
      Object returnValue = null;
      if (returnNode != null) {
         MethodBodyStatement mbs = (MethodBodyStatement)callNode.getNodeInfo().getActiveStatement();
         IProgramVariable resultVar = mbs.getResultVariable();
         if (resultVar != null) {
            // TODO: Compute result value with a side proof in that the result variable is assigned with correct SIMPLIFIED value.
//            returnValue = getValue(node.parent().parent(), resultVar);
         }
      }
      // Compute method name
      String name = createMethodReturnName(returnValue, ((ISEDMethodCall)callSEDNode).getName());
      // Create new node and fill it
      SEDMemoryMethodReturn newNode = new SEDMemoryMethodReturn(getDebugTarget(), thread, thread);
      fillNode(newNode, name, posInfo);
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
    * @param posInfo The {@link PositionInfo}.
    * @return {@code true} represent node as method call, {@code false} represent node as something else. 
    */
   protected boolean isMethodCallNode(Node node, NodeInfo info, SourceElement statement, PositionInfo posInfo) {
      if (statement instanceof MethodBodyStatement) {
         MethodBodyStatement mbs = (MethodBodyStatement)statement;
         ProgramMethod pm = mbs.getProgramMethod(proof.getServices());
         return !pm.isImplicit(); // Do not include implicit methods
      }
      else {
         return false;
      }
   }
   
   /**
    * Creates a new {@link ISEDMethodCall} for the given {@link MethodBodyStatement}.
    * @param statement The given {@link MethodBodyStatement} to represent as {@link ISEDMethodCall}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDMethodCall}.
    */
   protected ISEDMethodCall createMethodCallNode(MethodBodyStatement mbs, PositionInfo posInfo) {
      // Compute method name
      MethodReference mr = mbs.getMethodReference();
//      ProgramMethod pm = mbs.getProgramMethod(proof.getServices()); // TODO: Use whole method implementation location as position to select.
      String name = mr != null ? mr.toString() : UNKNOWN_METHOD_NAME;
      // Create new node and fill it
      SEDMemoryMethodCall newNode = new SEDMemoryMethodCall(getDebugTarget(), thread, thread);
      fillNode(newNode, name, posInfo);
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
      return posInfo != null && posInfo.getStartPosition() != Position.UNDEFINED; 
   }
   
   /**
    * Creates a new {@link ISEDStatement} for the given {@link SourceElement}.
    * @param statement The given {@link SourceElement} to represent as {@link ISEDStatement}.
    * @param posInfo The {@link PositionInfo} to use.
    * @return The created {@link ISEDStatement}.
    */
   protected ISEDStatement createStatementNode(SourceElement statement, PositionInfo posInfo) {
      // Compute statement name
      String name = statement.toString();
      // Create new node and fill it
      SEDMemoryStatement newNode = new SEDMemoryStatement(getDebugTarget(), thread, thread);
      fillNode(newNode, name, posInfo);
      return newNode;
   }
   
   /**
    * Fills the given {@link ISEDMemoryStackFrameCompatibleDebugNode} with the position information.
    * @param toFill The {@link ISEDMemoryStackFrameCompatibleDebugNode} to fill.
    * @param name The name to set.
    * @param posInfo The {@link PositionInfo} to set.
    */
   protected void fillNode(ISEDMemoryStackFrameCompatibleDebugNode toFill, String name, PositionInfo posInfo) {
      Assert.isNotNull(toFill);
      toFill.setName(name);
      if (posInfo != null && posInfo != PositionInfo.UNDEFINED) {
         if (posInfo.getEndPosition() != null) {
            toFill.setLineNumber(posInfo.getEndPosition().getLine());
         }
         if (posInfo.getFileName() != null) {
            toFill.setSourceName(new File(posInfo.getFileName()).getName());
         }
      }
   }
   
   /**
    * Adds the child to the parent.
    * @param parent The parent to add to.
    * @param child The child to add.
    */
   protected void addChild(ISEDDebugNode parent, ISEDDebugNode child) {
      if (parent instanceof SEDMemoryThread) {
         ((SEDMemoryThread)parent).addChild(child);
      }
      else if (parent instanceof SEDMemoryStatement) {
         ((SEDMemoryStatement)parent).addChild(child);
      }
      else if (parent instanceof SEDMemoryMethodCall) {
         ((SEDMemoryMethodCall)parent).addChild(child);
      }
      else if (parent instanceof SEDMemoryMethodReturn) {
         ((SEDMemoryMethodReturn)parent).addChild(child);
      }
      else if (parent instanceof SEDMemoryBranchCondition) {
         ((SEDMemoryBranchCondition)parent).addChild(child);
      }
      else if (parent instanceof SEDMemoryBranchNode) {
         ((SEDMemoryBranchNode)parent).addChild(child);
      }
      else if (parent instanceof SEDMemoryTermination) {
         ((SEDMemoryTermination)parent).addChild(child);
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
      // Remove proof from user interface
      KeYUtil.removeFromProofList(MainWindow.getInstance(), proof.env());
      // Remove auto mode listener
      MainWindow.getInstance().getMediator().removeAutoModeListener(autoModeListener);
      // Clear cache
      keyNodeMapping.clear();
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
            // Analyze proof
            analyzeProof(proof);
            // Inform UI that the process is suspended
            super.suspend();
         }
      }
      catch (DebugException exception) {
         LogUtil.getLogger().logError(exception);
      }
   }
}
