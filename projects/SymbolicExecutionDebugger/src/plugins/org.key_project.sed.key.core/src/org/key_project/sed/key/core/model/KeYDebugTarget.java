package org.key_project.sed.key.core.model;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

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
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
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
import org.key_project.sed.key.core.util.ASTNodeByEndIndexSearcher;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

/**
 * Implementation if {@link ISEDDebugTarget} which uses KeY to symbolically
 * debug a program.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYDebugTarget extends SEDMemoryDebugTarget {
   /**
    * The default name of the only contained {@link ISEDThread}.
    */
   public static final String DEFAULT_THREAD_NAME = "KeY Default Thread";
   
   /**
    * The used model identifier.
    */
   public static final String MODEL_IDENTIFIER = "org.key_project.sed.key.core";
   
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
    * If this is {@code true} an {@link ISEDMethodReturn} will contain the return value,
    * but the performance will suffer.
    * If it is {@code false} only the name of the returned method is shown in an {@link ISEDMethodReturn}.
    */
   private boolean showMethodReturnValuesInDebugNodes;
   
   /**
    * The {@link SymbolicExecutionTreeBuilder} which is used to extract
    * the symbolic execution tree from KeY's proof tree.
    */
   private SymbolicExecutionTreeBuilder builder;
   
   /**
    * Maps an {@link IExecutionNode} to its representation in the debug model.
    */
   private Map<IExecutionNode, ISEDMemoryDebugNode> executionToDebugMapping = new HashMap<IExecutionNode, ISEDMemoryDebugNode>();
   
   /**
    * Constructor.
    * @param launch The parent {@link ILaunch}.
    * @param proof The {@link Proof} in KeY to treat.
    * @param showMethodReturnValuesInDebugNodes
    * @throws DebugException Occurred Exception
    */
   public KeYDebugTarget(ILaunch launch, 
                         Proof proof, 
                         boolean showMethodReturnValuesInDebugNodes) throws DebugException {
      super(launch);
      // Update references
      Assert.isNotNull(proof);
      this.builder = new SymbolicExecutionTreeBuilder(proof);
      this.showMethodReturnValuesInDebugNodes = showMethodReturnValuesInDebugNodes; 
      // Update initial model
      setModelIdentifier(MODEL_IDENTIFIER);
      setName(proof.name() != null ? proof.name().toString() : "Unnamed");
      thread = new SEDMemoryThread(getDebugTarget());
      thread.setName(DEFAULT_THREAD_NAME);
      executionToDebugMapping.put(builder.getStartNode(), thread);
      addSymbolicThread(thread);
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
             KeYUtil.isProofInUI(builder.getProof()); // Otherwise Auto Mode is not available.
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
         StrategyProperties strategyProperties = SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(true, false, false, true);
         builder.getProof().setActiveStrategy(new SymbolicExecutionStrategy.Factory().create(builder.getProof(), strategyProperties));
         // Run proof
         KeYUtil.runProofInAutomaticModeWithoutResultDialog(builder.getProof());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return super.canSuspend() && 
             MainWindow.getInstance().frozen && // Only if the auto mode is in progress
             MainWindow.getInstance().getMediator().getProof() == builder.getProof(); // And the auto mode handles this proof
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
    * <p>
    * Synchronizes the execution tree extracted from KeY's proof via the
    * given {@link SymbolicExecutionTreeBuilder} with the debug model
    * which has the contained default {@link ISEDThread} as root.
    * </p>
    * <p>
    * The method iterates over the whole execution tree via an
    * {@link ExecutionNodePreorderIterator} and instantiates for each found
    * {@link IExecutionNode} an {@link ISEDDebugNode} via {@link #updateDebugModelNode(IExecutionNode)}.
    * </p>
    * @param builder The {@link SymbolicExecutionTreeBuilder} which provides the symbolic execution tree.
    * @throws DebugException Occurred Exception.
    */
   protected void updateDebugModel(SymbolicExecutionTreeBuilder builder) throws DebugException {
      // Update the symbolic execution tree
      builder.analyse();
      // Update the debug model
      ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(builder.getStartNode());
      while (iter.hasNext()) {
         IExecutionNode next = iter.next();
         if (!(next instanceof IExecutionStartNode)) { // Start not is always available as ISEDThread
            updateDebugModelNode(next);
         }
      }
   }
   
   /**
    * Updates the {@link ISEDDebugNode} which represents the given {@link IExecutionNode}.
    * If no {@link ISEDDebugNode} is available, a new one is created.
    * The mapping between debug and execution tree nodes is stored in {@link #executionToDebugMapping}.
    * @param executionNode The {@link IExecutionNode} to create an {@link ISEDDebugNode} for if required.
    * @throws DebugException Occurred Exception.
    */
   protected void updateDebugModelNode(IExecutionNode executionNode) throws DebugException {
      ISEDMemoryDebugNode debugNode = executionToDebugMapping.get(executionNode);
      if (debugNode == null) {
         ISEDMemoryDebugNode debugParent = executionToDebugMapping.get(executionNode.getParent());
         Assert.isNotNull(debugParent);
         if (executionNode instanceof IExecutionBranchCondition) {
            debugNode = createBranchCondition(debugParent, (IExecutionBranchCondition)executionNode);
         }
         else if (executionNode instanceof IExecutionBranchNode) {
            debugNode = createBranchNode(debugParent, (IExecutionBranchNode)executionNode);
         }
         else if (executionNode instanceof IExecutionLoopCondition) {
            debugNode = createLoopCondition(debugParent, (IExecutionLoopCondition)executionNode);
         }
         else if (executionNode instanceof IExecutionLoopNode) {
            debugNode = createLoopNode(debugParent, (IExecutionLoopNode)executionNode);
         }
         else if (executionNode instanceof IExecutionMethodCall) {
            debugNode = createMethodCall(debugParent, (IExecutionMethodCall)executionNode);
         }
         else if (executionNode instanceof IExecutionMethodReturn) {
            debugNode = createMethodReturn(debugParent, (IExecutionMethodReturn)executionNode);
         }
         else if (executionNode instanceof IExecutionStatement) {
            debugNode = createStatement(debugParent, (IExecutionStatement)executionNode);
         }
         else if (executionNode instanceof IExecutionTermination) {
            IExecutionTermination terminationExecutionNode = (IExecutionTermination)executionNode;
            if (terminationExecutionNode.isExceptionalTermination()) {
               debugNode = createExceptionalTermination(debugParent, terminationExecutionNode);
            }
            else {
               debugNode = createTermination(debugParent, terminationExecutionNode);
            }
         }
         else {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Not supported execution node \"" + executionNode + "\"."));
         }
         debugParent.addChild(debugNode);
         executionToDebugMapping.put(executionNode, debugNode);
      }
   }

   /**
    * Creates a new {@link SEDMemoryBranchCondition} for the given execution tree node.
    * @param debugParent The parent in the debug model.
    * @param executionNode The execution tree node which provides the relevant data.
    * @return The created debug model node.
    * @throws DebugException Occurred Exception.
    */
   protected SEDMemoryBranchCondition createBranchCondition(ISEDDebugNode debugParent, IExecutionBranchCondition executionNode) throws DebugException {
      SEDMemoryBranchCondition result = new SEDMemoryBranchCondition(this, debugParent, thread);
      result.setName(executionNode.getName());
      return result;
   }

   /**
    * Creates a new {@link SEDMemoryBranchNode} for the given execution tree node.
    * @param debugParent The parent in the debug model.
    * @param executionNode The execution tree node which provides the relevant data.
    * @return The created debug model node.
    * @throws DebugException Occurred Exception.
    */
   protected SEDMemoryBranchNode createBranchNode(ISEDDebugNode debugParent, IExecutionBranchNode executionNode) throws DebugException {
      // Create new node and fill it
      SEDMemoryBranchNode result = new SEDMemoryBranchNode(this, debugParent, thread);
      fillNode(result, executionNode.getName(), executionNode.getActivePositionInfo());
      // Try to update the position info with the position of the statement in JDT.
      updateLocationFromAST(result);
      return result;
   }

   /**
    * Creates a new {@link SEDMemoryExceptionalTermination} for the given execution tree node.
    * @param debugParent The parent in the debug model.
    * @param executionNode The execution tree node which provides the relevant data.
    * @return The created debug model node.
    * @throws DebugException Occurred Exception.
    */
   protected SEDMemoryExceptionalTermination createExceptionalTermination(ISEDDebugNode debugParent, IExecutionTermination executionNode) throws DebugException {
      SEDMemoryExceptionalTermination result = new SEDMemoryExceptionalTermination(this, debugParent, thread);
      result.setName(executionNode.getName());
      return result;
   }

   /**
    * Creates a new {@link SEDMemoryLoopCondition} for the given execution tree node.
    * @param debugParent The parent in the debug model.
    * @param executionNode The execution tree node which provides the relevant data.
    * @return The created debug model node.
    * @throws DebugException Occurred Exception.
    */
   protected SEDMemoryLoopCondition createLoopCondition(ISEDDebugNode debugParent, IExecutionLoopCondition executionNode) throws DebugException {
      // Create new node and fill it
      SEDMemoryLoopCondition result = new SEDMemoryLoopCondition(this, debugParent, thread);
      fillNode(result, executionNode.getName(), executionNode.getGuardExpressionPositionInfo());
      // Try to update the position info with the position of the statement in JDT.
      updateLocationFromAST(result);
      // Boolean literals have no position info, set the file of the statement without location in this case
      if (result.getSourceName() == null) {
         if (executionNode.getActivePositionInfo().getFileName() != null) {
            File file = new File(executionNode.getActivePositionInfo().getFileName());
            result.setSourceName(file.getName());
         }
      }
      return result;
   }

   /**
    * Creates a new {@link SEDMemoryLoopNode} for the given execution tree node.
    * @param debugParent The parent in the debug model.
    * @param executionNode The execution tree node which provides the relevant data.
    * @return The created debug model node.
    * @throws DebugException Occurred Exception.
    */
   protected SEDMemoryLoopNode createLoopNode(ISEDDebugNode debugParent, IExecutionLoopNode executionNode) throws DebugException {
      // Create new node and fill it
      SEDMemoryLoopNode result = new SEDMemoryLoopNode(this, debugParent, thread);
      fillNode(result, executionNode.getName(), executionNode.getActivePositionInfo());
      // Try to update the position info with the position of the statement in JDT.
      updateLocationFromAST(result);
      return result;
   }

   /**
    * Creates a new {@link SEDMemoryMethodCall} for the given execution tree node.
    * @param debugParent The parent in the debug model.
    * @param executionNode The execution tree node which provides the relevant data.
    * @return The created debug model node.
    * @throws DebugException Occurred Exception.
    */
   protected SEDMemoryMethodCall createMethodCall(ISEDDebugNode debugParent, IExecutionMethodCall executionNode) throws DebugException {
      SEDMemoryMethodCall result = new SEDMemoryMethodCall(this, debugParent, thread);
      fillNode(result, executionNode.getName(), executionNode.getProgramMethod().getPositionInfo());
      // Try to update the position info with the position of the method name
      // provided by JDT.
      try {
         if (result.getCharEnd() >= 0) {
            ICompilationUnit compilationUnit = findCompilationUnit(result);
            if (compilationUnit != null) {
               IMethod method = findJDTMethod(compilationUnit, result.getCharEnd());
               if (method != null) {
                  ISourceRange range = method.getNameRange();
                  result.setLineNumber(-1);
                  result.setCharStart(range.getOffset());
                  result.setCharEnd(range.getOffset() + range.getLength());
               }
            }
         }
      }
      catch (Exception e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
      return result;
   }

   /**
    * Creates a new {@link SEDMemoryMethodReturn} for the given execution tree node.
    * @param debugParent The parent in the debug model.
    * @param executionNode The execution tree node which provides the relevant data.
    * @return The created debug model node.
    * @throws DebugException Occurred Exception.
    */
   protected SEDMemoryMethodReturn createMethodReturn(ISEDDebugNode debugParent, IExecutionMethodReturn executionNode) throws DebugException {
      try {
         SEDMemoryMethodReturn result = new SEDMemoryMethodReturn(this, debugParent, thread);
         fillNode(result, 
                  showMethodReturnValuesInDebugNodes ? executionNode.getNameIncludingReturnValue() : executionNode.getName(), 
                  executionNode.getActivePositionInfo());
         // Update location with the location provided by the call node
         ISEDMethodCall callSEDNode = (ISEDMethodCall)executionToDebugMapping.get(executionNode.getMethodCall());
         Assert.isTrue(callSEDNode instanceof ISourceNameProvider);
         result.setSourceName(((ISourceNameProvider)callSEDNode).getSourceName());
         result.setLineNumber(callSEDNode.getLineNumber());
         result.setCharStart(callSEDNode.getCharStart());
         result.setCharEnd(callSEDNode.getCharEnd());
         return result;
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't compute method return value.", e));
      }
   }

   /**
    * Creates a new {@link SEDMemoryStatement} for the given execution tree node.
    * @param debugParent The parent in the debug model.
    * @param executionNode The execution tree node which provides the relevant data.
    * @return The created debug model node.
    * @throws DebugException Occurred Exception.
    */
   protected SEDMemoryStatement createStatement(ISEDDebugNode debugParent, IExecutionStatement executionNode) throws DebugException {
      // Create new node and fill it
      SEDMemoryStatement result = new SEDMemoryStatement(this, debugParent, thread);
      fillNode(result, executionNode.getName(), executionNode.getActivePositionInfo());
      // Try to update the position info with the position of the statement in JDT.
      updateLocationFromAST(result);
      return result;
   }

   /**
    * Creates a new {@link SEDMemoryTermination} for the given execution tree node.
    * @param debugParent The parent in the debug model.
    * @param executionNode The execution tree node which provides the relevant data.
    * @return The created debug model node.
    * @throws DebugException Occurred Exception.
    */
   protected SEDMemoryTermination createTermination(ISEDDebugNode debugParent, IExecutionTermination executionNode) throws DebugException {
      SEDMemoryTermination result = new SEDMemoryTermination(this, debugParent, thread);
      result.setName(executionNode.getName());
      return result;
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
      KeYUtil.removeFromProofList(main, builder.getProof().env());
      // Clear cache
      builder.dispose();
      builder = null;
      executionToDebugMapping.clear();
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
         if (e.getSource() == builder.getProof()) {
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
         if (e.getSource() == builder.getProof()) {
            updateDebugModel(builder);
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
