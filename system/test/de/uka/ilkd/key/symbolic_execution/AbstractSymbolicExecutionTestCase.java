package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Properties;
import java.util.Set;

import javax.xml.parsers.ParserConfigurationException;

import junit.framework.TestCase;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepOverSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepReturnSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Provides the basic functionality of {@link TestCase}s which tests
 * the symbolic execution features.
 * @author Martin Hentschel
 */
public class AbstractSymbolicExecutionTestCase extends TestCase {
   /**
    * <p>
    * If this constant is {@code true} a temporary directory is created with
    * new oracle files. The developer has than to copy the new required files
    * into the plug-in so that they are used during next test execution.
    * </p>
    * <p>
    * <b>Attention: </b> It is strongly required that new test scenarios
    * are verified with the SED application. If everything is fine a new test
    * method can be added to this class and the first test execution can be
    * used to generate the required oracle file. Existing oracle files should
    * only be replaced if the functionality of the Symbolic Execution Debugger
    * has changed so that they are outdated.
    * </p>
    */
   public static final boolean CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY = false;
   
   /**
    * The used temporary oracle directory.
    */
   protected static final File tempNewOracleDirectory;
   
   /**
    * The directory which contains the KeY repository.
    */
   protected static final File keyRepDirectory;
   
   /**
    * Creates the temporary oracle directory if required.
    */
   static {
      // Create temporary director for oracle files if required.
      File directory = null;
      try {
         if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            directory = File.createTempFile("SYMBOLIC_EXECUTION", "ORACLE_DIRECTORY");
            directory.delete();
            directory.mkdirs();
         }
      }
      catch (IOException e) {
      }
      tempNewOracleDirectory = directory;
      // Detect the KeY repository.
      // By default the repository should be the current path.
      // But in Eclipse development like for the symbolic execution debugger it is the eclipse plug-in.
      File currentDirectory = null;
      try {
         // Try to get key home directory from system property
         String keyProp = System.getProperty("key.home");
         if (keyProp != null)  {
            currentDirectory = new File(keyProp);
         }
         // Try to get it from customTargets.properties if plug-in org.key_project.key4eclipse is used.
         if (currentDirectory == null || !currentDirectory.isDirectory()) {
            File customTargets = new File(currentDirectory, "customTargets.properties"); 
            if (customTargets.isFile()) {
               // Extract repository directory from properties.
               Properties properties = new Properties();
               Reader reader = new FileReader(customTargets);
               try {
                  properties.load(reader);
               }
               finally {
                  reader.close();
               }
               final String KEY_REP_KEY = "key.rep";
               assertTrue("Value \"" + KEY_REP_KEY + "\" is not defined in \"" + customTargets.getAbsolutePath() + "\".", properties.containsKey(KEY_REP_KEY));
               currentDirectory = new File(properties.getProperty(KEY_REP_KEY));
            }
         }
      }
      catch (IOException e) {
      }
      keyRepDirectory = currentDirectory;  
   }
   
   /**
    * Creates a new oracle file.
    * @param node The node to save as oracle file.
    * @param oraclePathInBaseDirFile The path in example directory.
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @throws IOException Occurred Exception
    * @throws ProofInputException Occurred Exception
    */
   protected static void createOracleFile(IExecutionNode node, 
                                          String oraclePathInBaseDirFile, 
                                          boolean saveVariables,
                                          boolean saveCallStack) throws IOException, ProofInputException {
      if (tempNewOracleDirectory != null && tempNewOracleDirectory.isDirectory()) {
         // Create sub folder structure
         File oracleFile = new File(tempNewOracleDirectory, oraclePathInBaseDirFile);
         oracleFile.getParentFile().mkdirs();
         // Create oracle file
         ExecutionNodeWriter writer = new ExecutionNodeWriter();
         writer.write(node, ExecutionNodeWriter.DEFAULT_ENCODING, oracleFile, saveVariables, saveCallStack);
         // Print message to the user.
         printOracleDirectory();
      }
   }
   
   /**
    * Prints {@link #tempNewOracleDirectory} to the user via {@link System#out}.
    */
   protected static void printOracleDirectory() {
      if (tempNewOracleDirectory != null) {
         final String HEADER_LINE = "Oracle Directory is:";
         final String PREFIX = "### ";
         final String SUFFIX = " ###";
         String path = tempNewOracleDirectory.toString();
         int length = Math.max(path.length(), HEADER_LINE.length());
         String borderLines = JavaUtil.createLine("#", PREFIX.length() + length + SUFFIX.length());
         System.out.println(borderLines);
         System.out.println(PREFIX + HEADER_LINE + JavaUtil.createLine(" ", length - HEADER_LINE.length()) + SUFFIX);
         System.out.println(PREFIX + path + JavaUtil.createLine(" ", length - path.length()) + SUFFIX);
         System.out.println(borderLines);
      }
   }

   /**
    * Makes sure that the given nodes and their subtrees contains the same content.
    * @param expected The expected {@link IExecutionNode}.
    * @param current The current {@link IExecutionNode}.
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @param compareChildOrder Is the order of children relevant?
    * @throws ProofInputException Occurred Exception.
    */
   public static void assertExecutionNodes(IExecutionNode expected, 
                                           IExecutionNode current,
                                           boolean compareVariables,
                                           boolean compareCallStack,
                                           boolean compareChildOrder) throws ProofInputException {
      if (compareChildOrder) {
         // Order of children must be the same.
         ExecutionNodePreorderIterator expectedIter = new ExecutionNodePreorderIterator(expected);
         ExecutionNodePreorderIterator currentIter = new ExecutionNodePreorderIterator(current);
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            IExecutionNode expectedNext = expectedIter.next();
            IExecutionNode currentNext = currentIter.next();
            assertExecutionNode(expectedNext, currentNext, true, compareVariables, compareCallStack);
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
      }
      else {
         // Order of children is not relevant.
         ExecutionNodePreorderIterator expectedIter = new ExecutionNodePreorderIterator(expected);
         Set<IExecutionNode> currentVisitedNodes = new HashSet<IExecutionNode>();
         while (expectedIter.hasNext()) {
            IExecutionNode expectedNext = expectedIter.next();
            IExecutionNode currentNext = searchExecutionNode(current, expectedNext);
            if (!currentVisitedNodes.add(currentNext)) {
               fail("Node " + currentNext + " visited twice.");
            }
            assertExecutionNode(expectedNext, currentNext, true, compareVariables, compareCallStack);
         }
         // Make sure that each current node was visited
         ExecutionNodePreorderIterator currentIter = new ExecutionNodePreorderIterator(current);
         while (currentIter.hasNext()) {
            IExecutionNode currentNext = currentIter.next();
            if (!currentVisitedNodes.remove(currentNext)) {
               fail("Node " + currentNext + " is not in expected model.");
            }
         }
         assertTrue(currentVisitedNodes.isEmpty());
      }
   }
   
   /**
    * Searches the direct or indirect child in subtree of the node to search in.
    * @param toSearchIn The node to search in.
    * @param childToSearch The node to search.
    * @return The found node.
    * @throws ProofInputException Occurred Exception.
    */
   protected static IExecutionNode searchExecutionNode(IExecutionNode toSearchIn, IExecutionNode childToSearch) throws ProofInputException {
      // Make sure that parameters are valid
      assertNotNull(toSearchIn);
      assertNotNull(childToSearch);
      // Collect parents
      Deque<IExecutionNode> parents = new LinkedList<IExecutionNode>();
      IExecutionNode parent = childToSearch;
      while (parent != null) {
         parents.addFirst(parent);
         parent = parent.getParent();
      }
      // Search children in parent order
      boolean afterFirst = false;
      for (IExecutionNode currentParent : parents) {
         if (afterFirst) {
            toSearchIn = searchDirectChildNode(toSearchIn, currentParent);
         }
         else {
            afterFirst = true;
         }
      }
      assertNotNull("Direct or indirect Child " + childToSearch + " is not contained in " + toSearchIn + ".", toSearchIn);
      return toSearchIn;
   }
   
   /**
    * Searches the direct child. Nodes are equal if the name and the element type is equal.
    * @param parentToSearchIn The parent to search in its children.
    * @param directChildToSearch The child to search.
    * @return The found child.
    * @throws ProofInputException Occurred Exception.
    */
   protected static IExecutionNode searchDirectChildNode(IExecutionNode parentToSearchIn, IExecutionNode directChildToSearch) throws ProofInputException {
      // Make sure that parameters are valid
      assertNotNull(parentToSearchIn);
      assertNotNull(directChildToSearch);
      // Search child
      IExecutionNode result = null;
      int i = 0;
      IExecutionNode[] children = parentToSearchIn.getChildren();
      while (result == null && i < children.length) {
         if (children[i].getName().equals(directChildToSearch.getName()) &&
             children[i].getElementType().equals(directChildToSearch.getElementType())) {
            result = children[i];
         }
         i++;
      }
      assertNotNull("Child " + directChildToSearch + " is not contained in " + parentToSearchIn + ".", result);
      return result;
   }

   /**
    * Makes sure that the given nodes contains the same content.
    * Children are not compared.
    * @param expected The expected {@link IExecutionNode}.
    * @param current The current {@link IExecutionNode}.
    * @param compareParent Compare also the parent node?
    * @param compareChildren Compare direct children?
    * @param compareVariables Compare variables?
    * @param compareCallStack Compare call stack?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertExecutionNode(IExecutionNode expected, 
                                             IExecutionNode current, 
                                             boolean compareParent,
                                             boolean compareVariables,
                                             boolean compareCallStack) throws ProofInputException {
      // Compare nodes
      assertNotNull(expected);
      assertNotNull(current);
      assertEquals(expected.getName(), current.getName());
      assertEquals(expected.isPathConditionChanged(), current.isPathConditionChanged());
      assertEquals(expected.getFormatedPathCondition(), current.getFormatedPathCondition());
      if (expected instanceof IExecutionBranchCondition) {
         assertTrue("Expected IExecutionBranchCondition but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionBranchCondition);
         assertEquals(((IExecutionBranchCondition)expected).getFormatedBranchCondition(), ((IExecutionBranchCondition)current).getFormatedBranchCondition());
         assertEquals(((IExecutionBranchCondition)expected).isMergedBranchCondition(), ((IExecutionBranchCondition)current).isMergedBranchCondition());
      }
      else if (expected instanceof IExecutionStartNode) {
         assertTrue("Expected IExecutionStartNode but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionStartNode);
      }
      else if (expected instanceof IExecutionTermination) {
         assertTrue("Expected IExecutionTermination but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionTermination);
         assertEquals(((IExecutionTermination)expected).isExceptionalTermination(), ((IExecutionTermination)current).isExceptionalTermination());
      }
      else if (expected instanceof IExecutionBranchNode) {
         assertTrue("Expected IExecutionBranchNode but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionBranchNode);
         assertVariables((IExecutionBranchNode)expected, (IExecutionBranchNode)current, compareVariables);
      }
      else if (expected instanceof IExecutionLoopCondition) {
         assertTrue("Expected IExecutionLoopCondition but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionLoopCondition);
         assertVariables((IExecutionLoopCondition)expected, (IExecutionLoopCondition)current, compareVariables);
      }
      else if (expected instanceof IExecutionLoopNode) {
         assertTrue("Expected IExecutionLoopNode but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionLoopNode);
         assertVariables((IExecutionLoopNode)expected, (IExecutionLoopNode)current, compareVariables);
      }
      else if (expected instanceof IExecutionMethodCall) {
         assertTrue("Expected IExecutionMethodCall but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionMethodCall);
         assertVariables((IExecutionMethodCall)expected, (IExecutionMethodCall)current, compareVariables);
      }
      else if (expected instanceof IExecutionMethodReturn) {
         assertTrue("Expected IExecutionMethodReturn but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionMethodReturn);
         assertTrue(((IExecutionMethodReturn)expected).getNameIncludingReturnValue() + " does not match " + ((IExecutionMethodReturn)current).getNameIncludingReturnValue(), JavaUtil.equalIgnoreWhiteSpace(((IExecutionMethodReturn)expected).getNameIncludingReturnValue(), ((IExecutionMethodReturn)current).getNameIncludingReturnValue()));
         assertVariables((IExecutionMethodReturn)expected, (IExecutionMethodReturn)current, compareVariables);
      }
      else if (expected instanceof IExecutionStatement) {
         assertTrue("Expected IExecutionStatement but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionStatement);
         assertVariables((IExecutionStatement)expected, (IExecutionStatement)current, compareVariables);
      }
      else {
         fail("Unknown execution node \"" + expected + "\".");
      }
      // Optionally compare call stack
      if (compareCallStack) {
         IExecutionNode[] expectedStack = expected.getCallStack();
         IExecutionNode[] currentStack = current.getCallStack();
         if (expectedStack != null) {
            assertNotNull("Call stack of \"" + current + "\" should not be null.", currentStack);
            assertEquals("Node: " + expected, expectedStack.length, currentStack.length);
            for (int i = 0; i < expectedStack.length; i++) {
               assertExecutionNode(expectedStack[i], currentStack[i], false, false, false);
            }
         }
         else{
            assertTrue("Call stack of \"" + current + "\" is \"" + Arrays.toString(currentStack) + "\" but should be null or empty.", currentStack == null || currentStack.length == 0);
         }
      }
      // Optionally compare parent
      if (compareParent) {
         assertExecutionNode(expected, current, false, compareVariables, compareCallStack);
      }
   }

   /**
    * Makes sure that the given nodes contains the same {@link IExecutionVariable}s.
    * @param expected The expected node.
    * @param current The current node.
    * @param compareVariables Compare variables?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertVariables(IExecutionStateNode<?> expected, IExecutionStateNode<?> current, boolean compareVariables) throws ProofInputException {
      if (compareVariables) {
         assertNotNull(expected);
         assertNotNull(current);
         IExecutionVariable[] expectedVariables = expected.getVariables();
         IExecutionVariable[] currentVariables = current.getVariables();
         assertEquals(expectedVariables.length, currentVariables.length);
         for (int i = 0; i < expectedVariables.length; i++) {
            assertVariable(expectedVariables[i], currentVariables[i], true, true);
         }
      }
   }

   /**
    * Makes sure that the given variables are the same.
    * @param expected The expected variable.
    * @param current The current variable.
    * @param compareParent Compare parent?
    * @param compareChildren Compare children?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertVariable(IExecutionVariable expected, 
                                        IExecutionVariable current,
                                        boolean compareParent, 
                                        boolean compareChildren) throws ProofInputException {
      if (expected != null) {
         assertNotNull(current);
         // Compare variable
         assertEquals(expected.isArrayIndex(), current.isArrayIndex());
         assertEquals(expected.getArrayIndex(), current.getArrayIndex());
         assertEquals(expected.getName(), current.getName());
         assertEquals(expected.getTypeString(), current.getTypeString());
         assertTrue(expected.getValueString() + " does not match " + current.getValueString(), JavaUtil.equalIgnoreWhiteSpace(expected.getValueString(), current.getValueString()));
         // Compare parent
         if (compareParent) {
            assertVariable(expected.getParentVariable(), current.getParentVariable(), false, false);
         }
         // Compare children
         if (compareChildren) {
            IExecutionVariable[] expectedChildVariables = expected.getChildVariables();
            IExecutionVariable[] currentChildVariables = current.getChildVariables();
            assertEquals(expectedChildVariables.length, currentChildVariables.length);
            for (int i = 0; i < expectedChildVariables.length; i++) {
               assertVariable(expectedChildVariables[i], currentChildVariables[i], compareParent, compareChildren);
            }
         }
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Executes an "step return" global on all goals on the given {@link SymbolicExecutionTreeBuilder}.
    * @param ui The {@link CustomConsoleUserInterface} to use.
    * @param builder The {@link SymbolicExecutionGoalChooser} to do step on.
    * @param oraclePathInBaseDirFile The oracle path.
    * @param oracleIndex The index of the current step.
    * @param oracleFileExtension The oracle file extension
    * @param baseDir The base directory for oracles.
    * @throws IOException Occurred Exception
    * @throws ProofInputException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected static void stepReturn(CustomConsoleUserInterface ui, 
                                    SymbolicExecutionTreeBuilder builder, 
                                    String oraclePathInBaseDirFile, 
                                    int oracleIndex, 
                                    String oracleFileExtension, 
                                    File baseDir) throws IOException, ProofInputException, ParserConfigurationException, SAXException {
      // Set stop condition to stop after a number of detected symbolic execution tree nodes instead of applied rules
      Proof proof = builder.getProof();
      CompoundStopCondition stopCondition = new CompoundStopCondition();
      stopCondition.addChildren(new ExecutedSymbolicExecutionTreeNodesStopCondition(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN));
      stopCondition.addChildren(new StepReturnSymbolicExecutionTreeNodesStopCondition());
      proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Run proof
      ui.startAndWaitForProof(proof);
      // Update symbolic execution tree 
      builder.analyse();
      // Test result
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile, oracleIndex, oracleFileExtension, baseDir);
   }
   
   /**
    * Executes an "step over" global on all goals on the given {@link SymbolicExecutionTreeBuilder}.
    * @param ui The {@link CustomConsoleUserInterface} to use.
    * @param builder The {@link SymbolicExecutionGoalChooser} to do step on.
    * @param oraclePathInBaseDirFile The oracle path.
    * @param oracleIndex The index of the current step.
    * @param oracleFileExtension The oracle file extension
    * @param baseDir The base directory for oracles.
    * @throws IOException Occurred Exception
    * @throws ProofInputException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected static void stepOver(CustomConsoleUserInterface ui, 
                                  SymbolicExecutionTreeBuilder builder, 
                                  String oraclePathInBaseDirFile, 
                                  int oracleIndex, 
                                  String oracleFileExtension, 
                                  File baseDir) throws IOException, ProofInputException, ParserConfigurationException, SAXException {
      // Set stop condition to stop after a number of detected symbolic execution tree nodes instead of applied rules
      Proof proof = builder.getProof();
      CompoundStopCondition stopCondition = new CompoundStopCondition();
      stopCondition.addChildren(new ExecutedSymbolicExecutionTreeNodesStopCondition(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN));
      stopCondition.addChildren(new StepOverSymbolicExecutionTreeNodesStopCondition());
      proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Run proof
      ui.startAndWaitForProof(proof);
      // Update symbolic execution tree 
      builder.analyse();
      // Test result
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile, oracleIndex, oracleFileExtension, baseDir);
   }
   
   /**
    * Executes an "step into" global on all goals on the given {@link SymbolicExecutionTreeBuilder}.
    * @param ui The {@link CustomConsoleUserInterface} to use.
    * @param builder The {@link SymbolicExecutionGoalChooser} to do step on.
    * @param oraclePathInBaseDirFile The oracle path.
    * @param oracleIndex The index of the current step.
    * @param oracleFileExtension The oracle file extension
    * @param baseDir The base directory for oracles.
    * @throws IOException Occurred Exception
    * @throws ProofInputException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected static void stepInto(CustomConsoleUserInterface ui, 
                                  SymbolicExecutionTreeBuilder builder, 
                                  String oraclePathInBaseDirFile, 
                                  int oracleIndex, 
                                  String oracleFileExtension, 
                                  File baseDir) throws IOException, ProofInputException, ParserConfigurationException, SAXException {
      // Set stop condition to stop after a number of detected symbolic execution tree nodes instead of applied rules
      Proof proof = builder.getProof();
      ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = new ExecutedSymbolicExecutionTreeNodesStopCondition(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_FOR_ONE_STEP);
      proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Run proof
      ui.startAndWaitForProof(proof);
      // Update symbolic execution tree 
      builder.analyse();
      // Test result
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile, oracleIndex, oracleFileExtension, baseDir);
   }
   
   /**
    * Makes sure that after a step the correct set tree is created.
    * @param builder The {@link SymbolicExecutionTreeBuilder} to test.
    * @param oraclePathInBaseDirFile The oracle path.
    * @param oracleIndex The index of the current step.
    * @param oracleFileExtension The oracle file extension
    * @param baseDir The base directory for oracles.
    * @throws IOException Occurred Exception
    * @throws ProofInputException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected static void assertSetTreeAfterStep(SymbolicExecutionTreeBuilder builder, 
                                                String oraclePathInBaseDirFile, 
                                                int oracleIndex, 
                                                String oracleFileExtension, 
                                                File baseDir) throws IOException, ProofInputException, ParserConfigurationException, SAXException {
      if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
         createOracleFile(builder.getStartNode(), oraclePathInBaseDirFile + "_" + oracleIndex + oracleFileExtension, false, false);
      }
      else {
         // Read oracle file
         File oracleFile = new File(baseDir, oraclePathInBaseDirFile + "_" + oracleIndex + oracleFileExtension);
         ExecutionNodeReader reader = new ExecutionNodeReader();
         IExecutionNode oracleRoot = reader.read(oracleFile);
         assertNotNull(oracleRoot);
         // Make sure that the created symbolic execution tree matches the expected one.
         assertExecutionNodes(oracleRoot, builder.getStartNode(), false, false, false);
      }
   }
   
   /**
    * Searches a {@link IProgramMethod} in the given {@link Services}.
    * @param services The {@link Services} to search in.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @return The first found {@link IProgramMethod} in the type.
    */
   protected static IProgramMethod searchProgramMethod(Services services, 
                                                      String containerTypeName, 
                                                      final String methodFullName) {
      JavaInfo javaInfo = services.getJavaInfo();
      KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
      assertNotNull(containerKJT);
      ImmutableList<IProgramMethod> pms = javaInfo.getAllProgramMethods(containerKJT);
      IProgramMethod pm = JavaUtil.search(pms, new IFilter<IProgramMethod>() {
         @Override
         public boolean select(IProgramMethod element) {
            return methodFullName.equals(element.getFullName());
         }
      });
      assertNotNull(pm);
      return pm;
   }
   
   /**
    * Creates a {@link SymbolicExecutionEnvironment} which consists
    * of loading a file to load, finding the method to proof, instantiation
    * of proof and creation with configuration of {@link SymbolicExecutionTreeBuilder}.
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @param mergeBranchConditions Merge branch conditions?
    * @return The created {@link SymbolicExecutionEnvironment}.
    * @throws ProofInputException Occurred Exception.
    * @throws FileNotFoundException Occurred Exception.
    */
   protected static SymbolicExecutionEnvironment<CustomConsoleUserInterface> createSymbolicExecutionEnvironment(File baseDir, 
                                                                                                                String javaPathInBaseDir, 
                                                                                                                String containerTypeName, 
                                                                                                                String methodFullName,
                                                                                                                boolean mergeBranchConditions) throws ProofInputException, FileNotFoundException {
      // Make sure that required files exists
      File javaFile = new File(baseDir, javaPathInBaseDir);
      assertTrue(javaFile.exists());
      // Create user interface
      CustomConsoleUserInterface ui = new CustomConsoleUserInterface(false);
      // Load java file
      InitConfig initConfig = ui.load(javaFile, null, null);
      // Search method to proof
      Services services = initConfig.getServices();
      IProgramMethod pm = searchProgramMethod(services, containerTypeName, methodFullName);
      // Create default contract for method to test
      FunctionalOperationContract contract = SymbolicExecutionUtil.createDefaultContract(services, pm, null);
      // Start proof
      ProofOblInput input = new FunctionalOperationContractPO(initConfig, (FunctionalOperationContract)contract, true);
      Proof proof = ui.createProof(initConfig, input);
      assertNotNull(proof);
      // Set strategy and goal chooser to use for auto mode
      SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);
      // Create symbolic execution tree which contains only the start node at beginning
      SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(ui.getMediator(), proof, mergeBranchConditions);
      builder.analyse();
      assertNotNull(builder.getStartNode());
      return new SymbolicExecutionEnvironment<CustomConsoleUserInterface>(ui, initConfig, builder);
   }
}
