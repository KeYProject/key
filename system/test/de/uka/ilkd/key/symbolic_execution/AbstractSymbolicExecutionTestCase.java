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

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Set;

import javax.xml.parsers.ParserConfigurationException;

import junit.framework.TestCase;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.core.AutoModeListener;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.configuration.ChoiceSettings;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Services.ITermProgramVariableCollectorFactory;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.TermProgramVariableCollectorKeepUpdatesForBreakpointconditions;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBlockStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionExceptionalMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturnValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodSubsetPO;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepOverSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.StepReturnSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomUserInterface;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.MiscTools;

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
    * If the fast mode is enabled the step wise creation of models is disabled.
    */
   public static final boolean FAST_MODE = true;
   
   /**
    * Number of executed SET nodes to execute all in one.
    */
   public static final int ALL_IN_ONE_RUN = ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN;

   /**
    * Number of executed SET nodes for only one SET node per auto mode run.
    */
   public static final int SINGLE_SET_NODE_RUN = ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_FOR_ONE_STEP;

   /**
    * Default stop conditions of executed SET nodes.
    */
   public static final int[] DEFAULT_MAXIMAL_SET_NODES_PER_RUN;
   
   /**
    * The used temporary oracle directory.
    */
   protected static final File tempNewOracleDirectory;
   
   /**
    * The directory which contains the KeY repository.
    */
   public static final File keyRepDirectory;
   
   /**
    * Creates the temporary oracle directory if required.
    */
   static {
      // Define fast mode
      if (FAST_MODE) {
         DEFAULT_MAXIMAL_SET_NODES_PER_RUN = new int[] {ALL_IN_ONE_RUN};
      }
      else {
         DEFAULT_MAXIMAL_SET_NODES_PER_RUN = new int[] {ALL_IN_ONE_RUN, SINGLE_SET_NODE_RUN};
      }
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
    * @param saveConstraints Save constraints?
    * @param saveVariables Save variables?
    * @param saveCallStack Save call stack?
    * @param saveReturnValues Save method return values?
    * @throws IOException Occurred Exception
    * @throws ProofInputException Occurred Exception
    */
   protected static void createOracleFile(IExecutionNode<?> node, 
                                          String oraclePathInBaseDirFile, 
                                          boolean saveConstraints,
                                          boolean saveVariables,
                                          boolean saveCallStack,
                                          boolean saveReturnValues) throws IOException, ProofInputException {
      if (tempNewOracleDirectory != null && tempNewOracleDirectory.isDirectory()) {
         // Create sub folder structure
         File oracleFile = new File(tempNewOracleDirectory, oraclePathInBaseDirFile);
         oracleFile.getParentFile().mkdirs();
         // Create oracle file
         ExecutionNodeWriter writer = new ExecutionNodeWriter();
         writer.write(node, ExecutionNodeWriter.DEFAULT_ENCODING, oracleFile, saveVariables, saveCallStack, saveReturnValues, saveConstraints);
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
    * @param compareReturnValues Compare return values?
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   public static void assertExecutionNodes(IExecutionNode<?> expected, 
                                           IExecutionNode<?> current,
                                           boolean compareVariables,
                                           boolean compareCallStack,
                                           boolean compareChildOrder,
                                           boolean compareReturnValues,
                                           boolean compareConstraints) throws ProofInputException {
      if (compareChildOrder) {
         // Order of children must be the same.
         ExecutionNodePreorderIterator expectedIter = new ExecutionNodePreorderIterator(expected);
         ExecutionNodePreorderIterator currentIter = new ExecutionNodePreorderIterator(current);
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            IExecutionNode<?> expectedNext = expectedIter.next();
            IExecutionNode<?> currentNext = currentIter.next();
            assertExecutionNode(expectedNext, currentNext, true, compareVariables, compareCallStack, compareReturnValues, compareConstraints);
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
      }
      else {
         // Order of children is not relevant.
         ExecutionNodePreorderIterator expectedIter = new ExecutionNodePreorderIterator(expected);
         Set<IExecutionNode<?>> currentVisitedNodes = new LinkedHashSet<IExecutionNode<?>>();
         while (expectedIter.hasNext()) {
            IExecutionNode<?> expectedNext = expectedIter.next();
            IExecutionNode<?> currentNext = searchExecutionNode(current, expectedNext);
            if (!currentVisitedNodes.add(currentNext)) {
               fail("Node " + currentNext + " visited twice.");
            }
            assertExecutionNode(expectedNext, currentNext, true, compareVariables, compareCallStack, compareReturnValues, compareConstraints);
         }
         // Make sure that each current node was visited
         ExecutionNodePreorderIterator currentIter = new ExecutionNodePreorderIterator(current);
         while (currentIter.hasNext()) {
            IExecutionNode<?> currentNext = currentIter.next();
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
   protected static IExecutionNode<?> searchExecutionNode(IExecutionNode<?> toSearchIn, IExecutionNode<?> childToSearch) throws ProofInputException {
      // Make sure that parameters are valid
      assertNotNull(toSearchIn);
      assertNotNull(childToSearch);
      // Collect parents
      Deque<IExecutionNode<?>> parents = new LinkedList<IExecutionNode<?>>();
      IExecutionNode<?> parent = childToSearch;
      while (parent != null) {
         parents.addFirst(parent);
         parent = parent.getParent();
      }
      // Search children in parent order
      boolean afterFirst = false;
      for (IExecutionNode<?> currentParent : parents) {
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
   protected static IExecutionNode<?> searchDirectChildNode(IExecutionNode<?> parentToSearchIn, IExecutionNode<?> directChildToSearch) throws ProofInputException {
      // Make sure that parameters are valid
      assertNotNull(parentToSearchIn);
      assertNotNull(directChildToSearch);
      // Search child
      IExecutionNode<?> result = null;
      int i = 0;
      IExecutionNode<?>[] children = parentToSearchIn.getChildren();
      while (result == null && i < children.length) {
         if (children[i] instanceof IExecutionBranchCondition && directChildToSearch instanceof IExecutionBranchCondition) {
            if (JavaUtil.equalIgnoreWhiteSpace(children[i].getName(), directChildToSearch.getName()) &&
                JavaUtil.equalIgnoreWhiteSpace(((IExecutionBranchCondition)children[i]).getAdditionalBranchLabel(), ((IExecutionBranchCondition)directChildToSearch).getAdditionalBranchLabel()) &&
                children[i].getElementType().equals(directChildToSearch.getElementType())) {
                 result = children[i];
              }
         }
         else{
            if (JavaUtil.equalIgnoreWhiteSpace(children[i].getName(), directChildToSearch.getName()) &&
                  children[i].getElementType().equals(directChildToSearch.getElementType())) {
                 result = children[i];
              }
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
    * @param compareReturnValues Compare return values?
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertExecutionNode(IExecutionNode<?> expected, 
                                             IExecutionNode<?> current, 
                                             boolean compareParent,
                                             boolean compareVariables,
                                             boolean compareCallStack,
                                             boolean compareReturnValues,
                                             boolean compareConstraints) throws ProofInputException {
      // Compare nodes
      assertNotNull(expected);
      assertNotNull(current);
      assertTrue("Expected \"" + expected.getName() + "\" but is \"" + current.getName() + "\".", JavaUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
      assertEquals(expected.isPathConditionChanged(), current.isPathConditionChanged());
      assertTrue("Expected \"" + expected.getFormatedPathCondition() + "\" but is \"" + current.getFormatedPathCondition() + "\".", JavaUtil.equalIgnoreWhiteSpace(expected.getFormatedPathCondition(), current.getFormatedPathCondition()));
      if (compareParent) {
         if (expected instanceof IExecutionBlockStartNode<?>) {
            assertTrue(current instanceof IExecutionBlockStartNode<?>);
            assertEquals(((IExecutionBlockStartNode<?>)expected).isBlockOpened(), ((IExecutionBlockStartNode<?>)current).isBlockOpened());
            assertBlockCompletions((IExecutionBlockStartNode<?>)expected, (IExecutionBlockStartNode<?>)current);
         }
         assertCompletedBlocks(expected, current);
      }
      if (expected instanceof IExecutionBaseMethodReturn<?>) {
         assertTrue(current instanceof IExecutionBaseMethodReturn<?>);
         assertCallStateVariables((IExecutionBaseMethodReturn<?>) expected, (IExecutionBaseMethodReturn<?>) current, compareVariables, compareConstraints);
      }
      if (expected instanceof IExecutionBranchCondition) {
         assertTrue("Expected IExecutionBranchCondition but is " + current.getClass() + ".", current instanceof IExecutionBranchCondition);
         assertTrue("Expected \"" + ((IExecutionBranchCondition)expected).getFormatedBranchCondition() + "\" but is \"" + ((IExecutionBranchCondition)current).getFormatedBranchCondition() + "\".", JavaUtil.equalIgnoreWhiteSpace(((IExecutionBranchCondition)expected).getFormatedBranchCondition(), ((IExecutionBranchCondition)current).getFormatedBranchCondition()));
         assertEquals(((IExecutionBranchCondition)expected).isMergedBranchCondition(), ((IExecutionBranchCondition)current).isMergedBranchCondition());
         assertEquals(((IExecutionBranchCondition)expected).isBranchConditionComputed(), ((IExecutionBranchCondition)current).isBranchConditionComputed());
         assertTrue("Expected \"" + ((IExecutionBranchCondition)expected).getAdditionalBranchLabel() + "\" but is \"" + ((IExecutionBranchCondition)current).getAdditionalBranchLabel() + "\".", JavaUtil.equalIgnoreWhiteSpace(((IExecutionBranchCondition)expected).getAdditionalBranchLabel(), ((IExecutionBranchCondition)current).getAdditionalBranchLabel()));
         assertVariables((IExecutionBranchCondition)expected, (IExecutionBranchCondition)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionBranchCondition)expected, (IExecutionBranchCondition)current, compareConstraints);
      }
      else if (expected instanceof IExecutionStart) {
         assertTrue("Expected IExecutionStartNode but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionStart);
         assertTerminations((IExecutionStart)expected, (IExecutionStart)current);
         assertVariables((IExecutionStart)expected, (IExecutionStart)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionStart)expected, (IExecutionStart)current, compareConstraints);
      }
      else if (expected instanceof IExecutionTermination) {
         assertTrue("Expected IExecutionTermination but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionTermination);
         assertEquals(((IExecutionTermination)expected).getTerminationKind(), ((IExecutionTermination)current).getTerminationKind());
         assertEquals(((IExecutionTermination)expected).isBranchVerified(), ((IExecutionTermination)current).isBranchVerified());
         assertVariables((IExecutionTermination)expected, (IExecutionTermination)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionTermination)expected, (IExecutionTermination)current, compareConstraints);
      }
      else if (expected instanceof IExecutionBranchStatement) {
         assertTrue("Expected IExecutionBranchStatement but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionBranchStatement);
         assertVariables((IExecutionBranchStatement)expected, (IExecutionBranchStatement)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionBranchStatement)expected, (IExecutionBranchStatement)current, compareConstraints);
      }
      else if (expected instanceof IExecutionLoopCondition) {
         assertTrue("Expected IExecutionLoopCondition but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionLoopCondition);
         assertVariables((IExecutionLoopCondition)expected, (IExecutionLoopCondition)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionLoopCondition)expected, (IExecutionLoopCondition)current, compareConstraints);
      }
      else if (expected instanceof IExecutionLoopStatement) {
         assertTrue("Expected IExecutionLoopStatement but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionLoopStatement);
         assertVariables((IExecutionLoopStatement)expected, (IExecutionLoopStatement)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionLoopStatement)expected, (IExecutionLoopStatement)current, compareConstraints);
      }
      else if (expected instanceof IExecutionMethodCall) {
         assertTrue("Expected IExecutionMethodCall but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionMethodCall);
         assertVariables((IExecutionMethodCall)expected, (IExecutionMethodCall)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionMethodCall)expected, (IExecutionMethodCall)current, compareConstraints);
         assertMethodReturns((IExecutionMethodCall)expected, (IExecutionMethodCall)current);
      }
      else if (expected instanceof IExecutionMethodReturn) {
         assertTrue("Expected IExecutionMethodReturn but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionMethodReturn);
         assertTrue(((IExecutionMethodReturn)expected).getSignature() + " does not match " + ((IExecutionMethodReturn)current).getSignature(), JavaUtil.equalIgnoreWhiteSpace(((IExecutionMethodReturn)expected).getSignature(), ((IExecutionMethodReturn)current).getSignature()));
         if (compareReturnValues) {
            assertTrue(((IExecutionMethodReturn)expected).getNameIncludingReturnValue() + " does not match " + ((IExecutionMethodReturn)current).getNameIncludingReturnValue(), JavaUtil.equalIgnoreWhiteSpace(((IExecutionMethodReturn)expected).getNameIncludingReturnValue(), ((IExecutionMethodReturn)current).getNameIncludingReturnValue()));
            assertTrue(((IExecutionMethodReturn)expected).getSignatureIncludingReturnValue() + " does not match " + ((IExecutionMethodReturn)current).getSignatureIncludingReturnValue(), JavaUtil.equalIgnoreWhiteSpace(((IExecutionMethodReturn)expected).getSignatureIncludingReturnValue(), ((IExecutionMethodReturn)current).getSignatureIncludingReturnValue()));
            assertEquals(((IExecutionMethodReturn)expected).isReturnValuesComputed(), ((IExecutionMethodReturn)current).isReturnValuesComputed());
         }
         assertTrue(((IExecutionMethodReturn)expected).getFormatedMethodReturnCondition() + " does not match " + ((IExecutionMethodReturn)current).getFormatedMethodReturnCondition(), JavaUtil.equalIgnoreWhiteSpace(((IExecutionMethodReturn)expected).getFormatedMethodReturnCondition(), ((IExecutionMethodReturn)current).getFormatedMethodReturnCondition()));
         assertVariables((IExecutionMethodReturn)expected, (IExecutionMethodReturn)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionMethodReturn)expected, (IExecutionMethodReturn)current, compareConstraints);
         if (compareReturnValues) {
            assertReturnValues(((IExecutionMethodReturn)expected).getReturnValues(), ((IExecutionMethodReturn)current).getReturnValues());
         }
      }
      else if (expected instanceof IExecutionExceptionalMethodReturn) {
         assertTrue("Expected IExecutionExceptionalMethodReturn but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionExceptionalMethodReturn);
         assertTrue(((IExecutionExceptionalMethodReturn)expected).getSignature() + " does not match " + ((IExecutionExceptionalMethodReturn)current).getSignature(), JavaUtil.equalIgnoreWhiteSpace(((IExecutionExceptionalMethodReturn)expected).getSignature(), ((IExecutionExceptionalMethodReturn)current).getSignature()));
         assertTrue(((IExecutionExceptionalMethodReturn)expected).getFormatedMethodReturnCondition() + " does not match " + ((IExecutionExceptionalMethodReturn)current).getFormatedMethodReturnCondition(), JavaUtil.equalIgnoreWhiteSpace(((IExecutionExceptionalMethodReturn)expected).getFormatedMethodReturnCondition(), ((IExecutionExceptionalMethodReturn)current).getFormatedMethodReturnCondition()));
         assertVariables((IExecutionExceptionalMethodReturn)expected, (IExecutionExceptionalMethodReturn)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionExceptionalMethodReturn)expected, (IExecutionExceptionalMethodReturn)current, compareConstraints);
      }
      else if (expected instanceof IExecutionStatement) {
         assertTrue("Expected IExecutionStatement but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionStatement);
         assertVariables((IExecutionStatement)expected, (IExecutionStatement)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionStatement)expected, (IExecutionStatement)current, compareConstraints);
      }
      else if (expected instanceof IExecutionOperationContract) {
         assertTrue("Expected IExecutionOperationContract but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionOperationContract);
         assertEquals(((IExecutionOperationContract)expected).isPreconditionComplied(), ((IExecutionOperationContract)current).isPreconditionComplied());
         assertEquals(((IExecutionOperationContract)expected).hasNotNullCheck(), ((IExecutionOperationContract)current).hasNotNullCheck());
         assertEquals(((IExecutionOperationContract)expected).isNotNullCheckComplied(), ((IExecutionOperationContract)current).isNotNullCheckComplied());
         assertEquals(((IExecutionOperationContract)expected).getFormatedResultTerm(), ((IExecutionOperationContract)current).getFormatedResultTerm());
         assertEquals(((IExecutionOperationContract)expected).getFormatedExceptionTerm(), ((IExecutionOperationContract)current).getFormatedExceptionTerm());
         assertEquals(((IExecutionOperationContract)expected).getFormatedSelfTerm(), ((IExecutionOperationContract)current).getFormatedSelfTerm());
         assertEquals(((IExecutionOperationContract)expected).getFormatedContractParams(), ((IExecutionOperationContract)current).getFormatedContractParams());
         assertVariables((IExecutionOperationContract)expected, (IExecutionOperationContract)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionOperationContract)expected, (IExecutionOperationContract)current, compareConstraints);
      }
      else if (expected instanceof IExecutionLoopInvariant) {
         assertTrue("Expected IExecutionLoopInvariant but is " + (current != null ? current.getClass() : null) + ".", current instanceof IExecutionLoopInvariant);
         assertEquals(((IExecutionLoopInvariant)expected).isInitiallyValid(), ((IExecutionLoopInvariant)current).isInitiallyValid());
         assertVariables((IExecutionLoopInvariant)expected, (IExecutionLoopInvariant)current, compareVariables, compareConstraints);
         assertConstraints((IExecutionLoopInvariant)expected, (IExecutionLoopInvariant)current, compareConstraints);
      }
      else {
         fail("Unknown execution node \"" + expected + "\".");
      }
      // Optionally compare call stack
      if (compareCallStack) {
         IExecutionNode<?>[] expectedStack = expected.getCallStack();
         IExecutionNode<?>[] currentStack = current.getCallStack();
         if (expectedStack != null) {
            assertNotNull("Call stack of \"" + current + "\" should not be null.", currentStack);
            assertEquals("Node: " + expected, expectedStack.length, currentStack.length);
            for (int i = 0; i < expectedStack.length; i++) {
               assertExecutionNode(expectedStack[i], currentStack[i], false, false, false, false, false);
            }
         }
         else{
            assertTrue("Call stack of \"" + current + "\" is \"" + Arrays.toString(currentStack) + "\" but should be null or empty.", currentStack == null || currentStack.length == 0);
         }
      }
      // Optionally compare parent
      if (compareParent) {
         assertExecutionNode(expected, current, false, compareVariables, compareCallStack, compareReturnValues, compareConstraints);
      }
   }

   /**
    * Compares the completed blocks.
    * @param expected The expected {@link IExecutionNode}.
    * @param current The current {@link IExecutionNode}.
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertCompletedBlocks(IExecutionNode<?> expected, IExecutionNode<?> current) throws ProofInputException {
      ImmutableList<IExecutionBlockStartNode<?>> expectedEntries = expected.getCompletedBlocks();
      ImmutableList<IExecutionBlockStartNode<?>> currentEntries = current.getCompletedBlocks();
      if (expectedEntries != null) {
         assertNotNull("Completed blocks of \"" + current + "\" should not be null.", currentEntries);
         assertEquals("Node: " + expected, expectedEntries.size(), currentEntries.size());
         Iterator<IExecutionBlockStartNode<?>> expectedIter = expectedEntries.iterator();
         Iterator<IExecutionBlockStartNode<?>> currentIter = currentEntries.iterator();
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            IExecutionBlockStartNode<?> expectedNext = expectedIter.next();
            IExecutionBlockStartNode<?> currentNext = currentIter.next();
            assertExecutionNode(expectedNext, currentNext, false, false, false, false, false);
            String expectedCondition = expected.getFormatedBlockCompletionCondition(expectedNext);
            String currentCondition = current.getFormatedBlockCompletionCondition(currentNext);
            if (!JavaUtil.equalIgnoreWhiteSpace(expectedCondition, currentCondition)) {
               assertEquals(expectedCondition, currentCondition);
            }
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
      }
      else{
         assertTrue("Completed block entries of \"" + current + "\" is \"" + currentEntries + "\" but should be null or empty.", currentEntries == null || currentEntries.isEmpty());
      }
   }

   /**
    * Compares the block completions.
    * @param expected The expected {@link IExecutionBlockStartNode}.
    * @param current The current {@link IExecutionBlockStartNode}.
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertBlockCompletions(IExecutionBlockStartNode<?> expected, IExecutionBlockStartNode<?> current) throws ProofInputException {
      ImmutableList<IExecutionNode<?>> expectedEntries = expected.getBlockCompletions();
      ImmutableList<IExecutionNode<?>> currentEntries = current.getBlockCompletions();
      if (expectedEntries != null) {
         assertNotNull("Block completions of \"" + current + "\" should not be null.", currentEntries);
         assertEquals("Node: " + expected, expectedEntries.size(), currentEntries.size());
         Iterator<IExecutionNode<?>> expectedIter = expectedEntries.iterator();
         Iterator<IExecutionNode<?>> currentIter = currentEntries.iterator();
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            assertExecutionNode(expectedIter.next(), currentIter.next(), false, false, false, false, false);
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
      }
      else{
         assertTrue("Block completion entries of \"" + current + "\" is \"" + currentEntries + "\" but should be null or empty.", currentEntries == null || currentEntries.isEmpty());
      }
   }

   /**
    * Compares the method returns.
    * @param expected The expected {@link IExecutionMethodCall}.
    * @param current The current {@link IExecutionMethodCall}.
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertMethodReturns(IExecutionMethodCall expected, IExecutionMethodCall current) throws ProofInputException {
      ImmutableList<IExecutionBaseMethodReturn<?>> expectedEntries = expected.getMethodReturns();
      ImmutableList<IExecutionBaseMethodReturn<?>> currentEntries = current.getMethodReturns();
      if (expectedEntries != null) {
         assertNotNull("Method return of \"" + current + "\" should not be null.", currentEntries);
         assertEquals("Node: " + expected, expectedEntries.size(), currentEntries.size());
         Iterator<IExecutionBaseMethodReturn<?>> expectedIter = expectedEntries.iterator();
         Iterator<IExecutionBaseMethodReturn<?>> currentIter = currentEntries.iterator();
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            assertExecutionNode(expectedIter.next(), currentIter.next(), false, false, false, false, false);
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
      }
      else{
         assertTrue("Method return entries of \"" + current + "\" is \"" + currentEntries + "\" but should be null or empty.", currentEntries == null || currentEntries.isEmpty());
      }
   }

   /**
    * Compares the terminations.
    * @param expected The expected {@link IExecutionStart}.
    * @param current The current {@link IExecutionStart}.
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertTerminations(IExecutionStart expected, IExecutionStart current) throws ProofInputException {
      ImmutableList<IExecutionTermination> expectedEntries = expected.getTerminations();
      ImmutableList<IExecutionTermination> currentEntries = current.getTerminations();
      if (expectedEntries != null) {
         assertNotNull("Termination of \"" + current + "\" should not be null.", currentEntries);
         assertEquals("Node: " + expected, expectedEntries.size(), currentEntries.size());
         Iterator<IExecutionTermination> expectedIter = expectedEntries.iterator();
         Iterator<IExecutionTermination> currentIter = currentEntries.iterator();
         while (expectedIter.hasNext() && currentIter.hasNext()) {
            assertExecutionNode(expectedIter.next(), currentIter.next(), false, false, false, false, false);
         }
         assertFalse(expectedIter.hasNext());
         assertFalse(currentIter.hasNext());
      }
      else{
         assertTrue("Termination entries of \"" + current + "\" is \"" + currentEntries + "\" but should be null or empty.", currentEntries == null || currentEntries.isEmpty());
      }
   }

   /**
    * Makes sure that the given nodes contains the same {@link IExecutionMethodReturnValue}s.
    * @param expected The expected {@link IExecutionMethodReturnValue}s.
    * @param current The current {@link IExecutionMethodReturnValue}s.
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertReturnValues(IExecutionMethodReturnValue[] expected, IExecutionMethodReturnValue[] current) throws ProofInputException {
      assertNotNull(expected);
      assertNotNull(current);
      assertEquals(expected.length, current.length);
      for (int i = 0; i < expected.length; i++) {
         assertReturnValue(expected[i], current[i]);
      }
   }

   /**
    * Makes sure that the given {@link IExecutionMethodReturnValue}s are the same.
    * @param expected The expected {@link IExecutionMethodReturnValue}.
    * @param current The current {@link IExecutionMethodReturnValue}.
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertReturnValue(IExecutionMethodReturnValue expected, IExecutionMethodReturnValue current) throws ProofInputException {
      assertNotNull(expected);
      assertNotNull(current);
      assertTrue(expected.getName() + " does not match " + current.getName(), JavaUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
      assertTrue(expected.getReturnValueString() + " does not match " + current.getReturnValueString(), JavaUtil.equalIgnoreWhiteSpace(expected.getReturnValueString(), current.getReturnValueString()));
      assertEquals(expected.hasCondition(), current.hasCondition());
      assertTrue(expected.getConditionString() + " does not match " + current.getConditionString(), JavaUtil.equalIgnoreWhiteSpace(expected.getConditionString(), current.getConditionString()));
   }

   /**
    * Makes sure that the given nodes contains the same {@link IExecutionNode}s.
    * @param expected The expected node.
    * @param current The current node.
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertConstraints(IExecutionNode<?> expected, IExecutionNode<?> current, boolean compareConstraints) throws ProofInputException {
      if (compareConstraints) {
         assertNotNull(expected);
         assertNotNull(current);
         IExecutionConstraint[] expectedVariables = expected.getConstraints();
         IExecutionConstraint[] currentVariables = current.getConstraints();
         assertConstraints(expectedVariables, currentVariables);
      }
   }
   
   /**
    * Makes sure that the given constraints are the same.
    * @param expected The expected constraints.
    * @param current The current constraints.
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertConstraints(IExecutionConstraint[] expected, 
                                           IExecutionConstraint[] current) throws ProofInputException {
      TestCase.assertEquals(expected.length, current.length);
      // Compare ignore order
      List<IExecutionConstraint> availableCurrentVariables = new LinkedList<IExecutionConstraint>();
      JavaUtil.addAll(availableCurrentVariables, current);
      for (int i = 0; i < expected.length; i++) {
         final IExecutionConstraint expectedVariable = expected[i];
         // Find current variable with same name
         IExecutionConstraint currentVariable = JavaUtil.searchAndRemove(availableCurrentVariables, new IFilter<IExecutionConstraint>() {
            @Override
            public boolean select(IExecutionConstraint element) {
               try {
                  return JavaUtil.equalIgnoreWhiteSpace(expectedVariable.getName(), element.getName());
               }
               catch (ProofInputException e) {
                  throw new RuntimeException(e);
               }
            }
         });
         TestCase.assertNotNull(currentVariable);
         // Compare variables
         assertConstraint(expectedVariable, currentVariable);
      }
      TestCase.assertTrue(availableCurrentVariables.isEmpty());
   }

   /**
    * Makes sure that the given constraints are the same.
    * @param expected The expected constraint.
    * @param current The current constraint.
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertConstraint(IExecutionConstraint expected, 
                                          IExecutionConstraint current) throws ProofInputException {
      if (expected != null) {
         assertNotNull(current);
         if (!JavaUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName())) {
            assertEquals(expected.getName(), current.getName());
         }
      }
      else {
         assertNull(current);
      }
   }

   /**
    * Makes sure that the given nodes contains the same {@link IExecutionVariable}s of the call state.
    * @param expected The expected node.
    * @param current The current node.
    * @param compareVariables Compare variables?
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertCallStateVariables(IExecutionBaseMethodReturn<?> expected, IExecutionBaseMethodReturn<?> current, boolean compareVariables, boolean compareConstraints) throws ProofInputException {
      if (compareVariables) {
         assertNotNull(expected);
         assertNotNull(current);
         IExecutionVariable[] expectedVariables = expected.getCallStateVariables();
         IExecutionVariable[] currentVariables = current.getCallStateVariables();
         assertVariables(expectedVariables, currentVariables, true, true, compareConstraints);
      }
   }

   /**
    * Makes sure that the given nodes contains the same {@link IExecutionVariable}s.
    * @param expected The expected node.
    * @param current The current node.
    * @param compareVariables Compare variables?
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertVariables(IExecutionNode<?> expected, IExecutionNode<?> current, boolean compareVariables, boolean compareConstraints) throws ProofInputException {
      if (compareVariables) {
         assertNotNull(expected);
         assertNotNull(current);
         IExecutionVariable[] expectedVariables = expected.getVariables();
         IExecutionVariable[] currentVariables = current.getVariables();
         assertVariables(expectedVariables, currentVariables, true, true, compareConstraints);
      }
   }
   
   /**
    * Makes sure that the given variables are the same.
    * @param expected The expected variables.
    * @param current The current variables.
    * @param compareParent Compare parent?
    * @param compareChildren Compare children?
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertVariables(IExecutionVariable[] expected, 
                                         IExecutionVariable[] current,
                                         boolean compareParent, 
                                         boolean compareChildren,
                                         boolean compareConstraints) throws ProofInputException {
      TestCase.assertEquals(expected.length, current.length);
      // Compare ignore order
      List<IExecutionVariable> availableCurrentVariables = new LinkedList<IExecutionVariable>();
      JavaUtil.addAll(availableCurrentVariables, current);
      for (int i = 0; i < expected.length; i++) {
         final IExecutionVariable expectedVariable = expected[i];
         // Find current variable with same name
         IExecutionVariable currentVariable = JavaUtil.searchAndRemove(availableCurrentVariables, new IFilter<IExecutionVariable>() {
            @Override
            public boolean select(IExecutionVariable element) {
               try {
                  return JavaUtil.equalIgnoreWhiteSpace(expectedVariable.getName(), element.getName());
               }
               catch (ProofInputException e) {
                  throw new RuntimeException(e);
               }
            }
         });
         TestCase.assertNotNull(currentVariable);
         // Compare variables
         assertVariable(expectedVariable, currentVariable, compareParent, compareChildren, compareConstraints);
      }
      TestCase.assertTrue(availableCurrentVariables.isEmpty());
   }

   /**
    * Makes sure that the given variables are the same.
    * @param expected The expected variable.
    * @param current The current variable.
    * @param compareParent Compare parent?
    * @param compareChildren Compare children?
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertVariable(IExecutionVariable expected, 
                                        IExecutionVariable current,
                                        boolean compareParent, 
                                        boolean compareChildren,
                                        boolean compareConstraints) throws ProofInputException {
      if (expected != null) {
         assertNotNull(current);
         // Compare variable
         assertEquals(expected.isArrayIndex(), current.isArrayIndex());
         assertEquals(expected.getArrayIndexString(), current.getArrayIndexString());
         assertEquals(expected.getName(), current.getName());
         // Compare parent
         if (compareParent) {
            assertValue(expected.getParentValue(), current.getParentValue(), false, false, false);
         }
         // Compare children
         if (compareChildren) {
            IExecutionValue[] expectedValues = expected.getValues();
            IExecutionValue[] currentValues = current.getValues();
            assertValues(expectedValues, currentValues, true, true, compareConstraints);
         }
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Makes sure that the given values are the same.
    * @param expected The expected values.
    * @param current The current values.
    * @param compareParent Compare parent?
    * @param compareChildren Compare children?
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertValues(IExecutionValue[] expected, 
                                      IExecutionValue[] current,
                                      boolean compareParent, 
                                      boolean compareChildren,
                                      boolean compareConstraints) throws ProofInputException {
      TestCase.assertEquals(expected.length, current.length);
      // Compare ignore order
      List<IExecutionValue> availableCurrentVariables = new LinkedList<IExecutionValue>();
      JavaUtil.addAll(availableCurrentVariables, current);
      for (int i = 0; i < expected.length; i++) {
         final IExecutionValue expectedVariable = expected[i];
         // Find current variable with same name
         IExecutionValue currentVariable = JavaUtil.searchAndRemove(availableCurrentVariables, new IFilter<IExecutionValue>() {
            @Override
            public boolean select(IExecutionValue element) {
               try {
                  return JavaUtil.equalIgnoreWhiteSpace(expectedVariable.getName(), element.getName()) &&
                         JavaUtil.equalIgnoreWhiteSpace(expectedVariable.getConditionString(), element.getConditionString());
               }
               catch (ProofInputException e) {
                  throw new RuntimeException(e);
               }
            }
         });
         TestCase.assertNotNull(currentVariable);
         // Compare variables
         assertValue(expectedVariable, currentVariable, compareParent, compareChildren, compareConstraints);
      }
      TestCase.assertTrue(availableCurrentVariables.isEmpty());
   }
   
   /**
    * Makes sure that the given values are the same.
    * @param expected The expected variable.
    * @param current The current variable.
    * @param compareParent Compare parent?
    * @param compareChildren Compare children?
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertValue(IExecutionValue expected, 
                                     IExecutionValue current,
                                     boolean compareParent, 
                                     boolean compareChildren,
                                     boolean compareConstraints) throws ProofInputException {
      if (expected != null) {
         assertNotNull(current);
         // Compare variable
         assertTrue(expected.getName() + " does not match " + current.getName(), JavaUtil.equalIgnoreWhiteSpace(expected.getName(), current.getName()));
         assertEquals(expected.getTypeString(), current.getTypeString());
         assertTrue(expected.getValueString() + " does not match " + current.getValueString(), JavaUtil.equalIgnoreWhiteSpace(expected.getValueString(), current.getValueString()));
         assertEquals(expected.isValueAnObject(), current.isValueAnObject());
         assertEquals(expected.isValueUnknown(), current.isValueUnknown());
         assertTrue(expected.getConditionString() + " does not match " + current.getConditionString(), JavaUtil.equalIgnoreWhiteSpace(expected.getConditionString(), current.getConditionString()));
         // Compare parent
         if (compareParent) {
            assertVariable(expected.getVariable(), current.getVariable(), false, false, compareConstraints);
         }
         // Compare children
         if (compareChildren) {
            IExecutionVariable[] expectedChildVariables = expected.getChildVariables();
            IExecutionVariable[] currentChildVariables = current.getChildVariables();
            assertVariables(expectedChildVariables, currentChildVariables, compareParent, compareChildren, compareConstraints);
         }
         // Compare constraints
         if (compareConstraints) {
            IExecutionConstraint[] expectedConstraints = expected.getConstraints();
            IExecutionConstraint[] currentConstraints = current.getConstraints();
            assertConstraints(expectedConstraints, currentConstraints);
         }
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Executes an "step return" global on all goals on the given {@link SymbolicExecutionTreeBuilder}.
    * @param ui The {@link CustomUserInterface} to use.
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
   protected static void stepReturn(CustomUserInterface ui, 
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
      ui.startAndWaitForAutoMode(proof);
      // Update symbolic execution tree 
      builder.analyse();
      // Test result
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile, oracleIndex, oracleFileExtension, baseDir);
   }
   
   
   
   /**
    * Executes an "step return" global on all goals on the given {@link SymbolicExecutionTreeBuilder}.
    * @param ui The {@link CustomUserInterface} to use.
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
   protected static void stepReturnWithBreakpoints(CustomUserInterface ui, 
                                    SymbolicExecutionTreeBuilder builder, 
                                    String oraclePathInBaseDirFile, 
                                    int oracleIndex, 
                                    String oracleFileExtension, 
                                    File baseDir,
                                    CompoundStopCondition lineBreakpoints) throws IOException, ProofInputException, ParserConfigurationException, SAXException {
      // Set stop condition to stop after a number of detected symbolic execution tree nodes instead of applied rules
      Proof proof = builder.getProof();
      CompoundStopCondition stopCondition = new CompoundStopCondition();
      stopCondition.addChildren(new ExecutedSymbolicExecutionTreeNodesStopCondition(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN));
      stopCondition.addChildren(new StepReturnSymbolicExecutionTreeNodesStopCondition());
      stopCondition.addChildren(lineBreakpoints);
      proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Run proof
      ui.startAndWaitForAutoMode(proof);
      // Update symbolic execution tree 
      builder.analyse();
      // Test result
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile, oracleIndex, oracleFileExtension, baseDir);
   }
   
   /**
    * Executes an "step over" global on all goals on the given {@link SymbolicExecutionTreeBuilder}.
    * @param ui The {@link CustomUserInterface} to use.
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
   protected static void stepOver(CustomUserInterface ui, 
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
      ui.startAndWaitForAutoMode(proof);
      // Update symbolic execution tree 
      builder.analyse();
      // Test result
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile, oracleIndex, oracleFileExtension, baseDir);
   }
   
   /**
    * Executes an "step into" global on all goals on the given {@link SymbolicExecutionTreeBuilder}.
    * @param ui The {@link CustomUserInterface} to use.
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
   protected static void stepInto(CustomUserInterface ui, 
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
      ui.startAndWaitForAutoMode(proof);
      // Update symbolic execution tree 
      builder.analyse();
      // Test result
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile, oracleIndex, oracleFileExtension, baseDir);
   }
   
   /**
    * Executes an "step into" global on all goals on the given {@link SymbolicExecutionTreeBuilder}.
    * @param ui The {@link CustomUserInterface} to use.
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
   protected static void resume(CustomUserInterface ui, 
                                SymbolicExecutionTreeBuilder builder, 
                                String oraclePathInBaseDirFile, 
                                File baseDir) throws IOException, ProofInputException, ParserConfigurationException, SAXException {
      // Set stop condition to stop after a number of detected symbolic execution tree nodes instead of applied rules
      Proof proof = builder.getProof();
      ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = new ExecutedSymbolicExecutionTreeNodesStopCondition(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);
      proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Run proof
      ui.startAndWaitForAutoMode(proof);
      // Update symbolic execution tree 
      builder.analyse();
      // Test result
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile, baseDir);
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
                                                File baseDir) throws IOException, ProofInputException, ParserConfigurationException, SAXException {
      if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
         createOracleFile(builder.getStartNode(), oraclePathInBaseDirFile, false, false, false, false);
      }
      else {
         // Read oracle file
         File oracleFile = new File(baseDir, oraclePathInBaseDirFile);
         ExecutionNodeReader reader = new ExecutionNodeReader();
         IExecutionNode<?> oracleRoot = reader.read(oracleFile);
         assertNotNull(oracleRoot);
         // Make sure that the created symbolic execution tree matches the expected one.
         assertExecutionNodes(oracleRoot, builder.getStartNode(), false, false, false, false, false);
      }
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
      assertSetTreeAfterStep(builder, oraclePathInBaseDirFile + "_" + oracleIndex + oracleFileExtension, baseDir);
   }
   
   /**
    * Searches a {@link IProgramMethod} in the given {@link Services}.
    * @param services The {@link Services} to search in.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @return The first found {@link IProgramMethod} in the type.
    */
   public static IProgramMethod searchProgramMethod(Services services, 
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
      if (pm == null) {
         pms = javaInfo.getConstructors(containerKJT);
         pm = JavaUtil.search(pms, new IFilter<IProgramMethod>() {
            @Override
            public boolean select(IProgramMethod element) {
               return methodFullName.equals(element.getFullName());
            }
         });
      }
      assertNotNull(pm);
      return pm;
   }
   
   /**
    * Creates a {@link SymbolicExecutionEnvironment} which consists
    * of loading a file to load, finding the method to proof, instantiation
    * of proof and creation with configuration of {@link SymbolicExecutionTreeBuilder}.
    * @param baseDir The base directory which contains test and oracle file.
    * @param baseContractName The name of the contract.
    * @param methodFullName The method name to search.
    * @param mergeBranchConditions Merge branch conditions?
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvarints Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @return The created {@link SymbolicExecutionEnvironment}.
    * @throws ProblemLoaderException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   protected static SymbolicExecutionEnvironment<CustomUserInterface> createSymbolicExecutionEnvironment(File baseDir, 
                                                                                                         String javaPathInBaseDir, 
                                                                                                         String baseContractName,
                                                                                                         boolean mergeBranchConditions,
                                                                                                         boolean useOperationContracts,
                                                                                                         boolean useLoopInvarints,
                                                                                                         boolean nonExecutionBranchHidingSideProofs,
                                                                                                         boolean aliasChecks,
                                                                                                         boolean useUnicode,
                                                                                                         boolean usePrettyPrinting,
                                                                                                         boolean variablesAreOnlyComputedFromUpdates) throws ProblemLoaderException, ProofInputException {
      // Make sure that required files exists
      File javaFile = new File(baseDir, javaPathInBaseDir);
      assertTrue(javaFile.exists());
      // Load java file
      KeYEnvironment<CustomUserInterface> environment = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), javaFile, null, null);
      // Start proof
      final Contract contract = environment.getServices().getSpecificationRepository().getContractByName(baseContractName);
      assertTrue(contract instanceof FunctionalOperationContract);
      ProofOblInput input = new FunctionalOperationContractPO(environment.getInitConfig(), (FunctionalOperationContract)contract, true, true);
      Proof proof = environment.createProof(input);
      assertNotNull(proof);
      // Set strategy and goal chooser to use for auto mode
      SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN, useOperationContracts, useLoopInvarints, nonExecutionBranchHidingSideProofs, aliasChecks);
      // Create symbolic execution tree which contains only the start node at beginning
      SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(environment.getMediator(), proof, mergeBranchConditions, useUnicode, usePrettyPrinting, variablesAreOnlyComputedFromUpdates);
      builder.analyse();
      assertNotNull(builder.getStartNode());
      return new SymbolicExecutionEnvironment<CustomUserInterface>(environment, builder);
   }
   
   /**
    * Creates a {@link SymbolicExecutionEnvironment} which consists
    * of loading a file to load, finding the method to proof, instantiation
    * of proof and creation with configuration of {@link SymbolicExecutionTreeBuilder}.
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @param precondition An optional precondition to use.
    * @param mergeBranchConditions Merge branch conditions?
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvarints Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @return The created {@link SymbolicExecutionEnvironment}.
    * @throws ProblemLoaderException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   protected static SymbolicExecutionEnvironment<CustomUserInterface> createSymbolicExecutionEnvironment(File baseDir, 
                                                                                                         String javaPathInBaseDir, 
                                                                                                         String containerTypeName, 
                                                                                                         String methodFullName,
                                                                                                         String precondition,
                                                                                                         boolean mergeBranchConditions,
                                                                                                         boolean useOperationContracts,
                                                                                                         boolean useLoopInvarints,
                                                                                                         boolean nonExecutionBranchHidingSideProofs,
                                                                                                         boolean aliasChecks,
                                                                                                         boolean useUnicode,
                                                                                                         boolean usePrettyPrinting,
                                                                                                         boolean variablesAreOnlyComputedFromUpdates) throws ProblemLoaderException, ProofInputException {
      // Make sure that required files exists
      File javaFile = new File(baseDir, javaPathInBaseDir);
      assertTrue(javaFile.exists());
      // Load java file
      KeYEnvironment<CustomUserInterface> environment = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), javaFile, null, null);
      // Search method to proof
      IProgramMethod pm = searchProgramMethod(environment.getServices(), containerTypeName, methodFullName);
      // Start proof
      ProofOblInput input = new ProgramMethodPO(environment.getInitConfig(), pm.getFullName(), pm, precondition, true, true);
      Proof proof = environment.createProof(input);
      assertNotNull(proof);
      // Set strategy and goal chooser to use for auto mode
      SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN, useOperationContracts, useLoopInvarints, nonExecutionBranchHidingSideProofs, aliasChecks);
      // Create symbolic execution tree which contains only the start node at beginning
      SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(environment.getMediator(), proof, mergeBranchConditions, useUnicode, usePrettyPrinting, variablesAreOnlyComputedFromUpdates);
      builder.analyse();
      assertNotNull(builder.getStartNode());
      return new SymbolicExecutionEnvironment<CustomUserInterface>(environment, builder);
   }
   
   /**
    * Creates a {@link SymbolicExecutionEnvironment} which consists
    * of loading a proof file to load and creation with configuration of {@link SymbolicExecutionTreeBuilder}.
    * @param baseDir The base directory which contains test and oracle file.
    * @param proofPathInBaseDir The path to the proof file inside the base directory.
    * @param mergeBranchConditions Merge branch conditions?
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvarints Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @return The created {@link SymbolicExecutionEnvironment}.
    * @throws ProblemLoaderException Occurred Exception.
    */
   protected static SymbolicExecutionEnvironment<CustomUserInterface> createSymbolicExecutionEnvironment(File baseDir, 
                                                                                                         String proofPathInBaseDir, 
                                                                                                         boolean mergeBranchConditions,
                                                                                                         boolean useOperationContracts,
                                                                                                         boolean useLoopInvarints,
                                                                                                         boolean nonExecutionBranchHidingSideProofs,
                                                                                                         boolean aliasChecks,
                                                                                                         boolean useUnicode,
                                                                                                         boolean usePrettyPrinting,
                                                                                                         boolean variablesAreOnlyComputedFromUpdates) throws ProblemLoaderException {
      // Make sure that required files exists
      File proofFile = new File(baseDir, proofPathInBaseDir);
      assertTrue(proofFile.exists());
      // Load java file
      KeYEnvironment<CustomUserInterface> environment = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), proofFile, null, null, SymbolicExecutionTreeBuilder.createPoPropertiesToForce(), null);
      Proof proof = environment.getLoadedProof();
      assertNotNull(proof);
      // Set strategy and goal chooser to use for auto mode
      SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN, useOperationContracts, useLoopInvarints, nonExecutionBranchHidingSideProofs, aliasChecks);
      // Create symbolic execution tree which contains only the start node at beginning
      SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(environment.getMediator(), proof, mergeBranchConditions, useUnicode, usePrettyPrinting, variablesAreOnlyComputedFromUpdates);
      builder.analyse();
      assertNotNull(builder.getStartNode());
      return new SymbolicExecutionEnvironment<CustomUserInterface>(environment, builder);
   }
   
   /**
    * Creates a {@link SymbolicExecutionEnvironment} which consists
    * of loading a file to load, finding the method to proof, instantiation
    * of proof and creation with configuration of {@link SymbolicExecutionTreeBuilder}.
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The name of the type which contains the method.
    * @param methodFullName The method name to search.
    * @param precondition An optional precondition to use.
    * @param startPosition The start position.
    * @param endPosition The end position.
    * @param mergeBranchConditions Merge branch conditions?
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvarints Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @return The created {@link SymbolicExecutionEnvironment}.
    * @throws ProblemLoaderException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   protected static SymbolicExecutionEnvironment<CustomUserInterface> createSymbolicExecutionEnvironment(File baseDir, 
                                                                                                                String javaPathInBaseDir, 
                                                                                                                String containerTypeName, 
                                                                                                                String methodFullName,
                                                                                                                String precondition,
                                                                                                                Position startPosition,
                                                                                                                Position endPosition,
                                                                                                                boolean mergeBranchConditions,
                                                                                                                boolean useOperationContracts,
                                                                                                                boolean useLoopInvarints,
                                                                                                                boolean nonExecutionBranchHidingSideProofs,
                                                                                                                boolean aliasChecks,
                                                                                                                boolean useUnicode,
                                                                                                                boolean usePrettyPrinting,
                                                                                                                boolean variablesAreOnlyComputedFromUpdates) throws ProblemLoaderException, ProofInputException {
      // Make sure that required files exists
      File javaFile = new File(baseDir, javaPathInBaseDir);
      assertTrue(javaFile.exists());
      // Load java file
      KeYEnvironment<CustomUserInterface> environment = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), javaFile, null, null);
      // Search method to proof
      IProgramMethod pm = searchProgramMethod(environment.getServices(), containerTypeName, methodFullName);
      // Start proof
      ProofOblInput input = new ProgramMethodSubsetPO(environment.getInitConfig(), methodFullName, pm, precondition, startPosition, endPosition, true, true);
      Proof proof = environment.createProof(input);
      assertNotNull(proof);
      // Set strategy and goal chooser to use for auto mode
      SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN, useOperationContracts, useLoopInvarints, nonExecutionBranchHidingSideProofs, aliasChecks);
      // Create symbolic execution tree which contains only the start node at beginning
      SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(environment.getMediator(), proof, mergeBranchConditions, useUnicode, usePrettyPrinting, variablesAreOnlyComputedFromUpdates);
      builder.analyse();
      assertNotNull(builder.getStartNode());
      return new SymbolicExecutionEnvironment<CustomUserInterface>(environment, builder);
   }
   
   /**
    * Extracts the content of the try block from the initial {@link Sequent}.
    * @param proof The {@link Proof} which contains the initial {@link Sequent}:
    * @return The try content.
    */
   protected String getTryContent(Proof proof) {
      assertNotNull(proof);
      Node node = proof.root();
      Sequent sequent = node.sequent();
      assertEquals(1, sequent.succedent().size());
      Term succedent = sequent.succedent().get(0).formula();
      assertEquals(2, succedent.subs().size());
      Term updateApplication = succedent.subs().get(1);
      assertEquals(2, updateApplication.subs().size());
      JavaProgramElement updateContent = updateApplication.subs().get(1).javaBlock().program();
      assertTrue(updateContent instanceof StatementBlock);
      ImmutableArray<? extends Statement> updateContentBody = ((StatementBlock)updateContent).getBody();
      assertEquals(2, updateContentBody.size());
      assertTrue(updateContentBody.get(1) instanceof Try);
      Try tryStatement = (Try)updateContentBody.get(1);
      assertEquals(1, tryStatement.getBranchCount());
      return ProofSaver.printAnything(tryStatement.getBody(), proof.getServices());
   }
   
   /**
    * Makes sure that the save and loading process works.
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param oraclePathInBaseDirFile The oracle path.
    * @param env The already executed {@link SymbolicExecutionEnvironment} which contains the proof to save/load.
    * @throws IOException Occurred Exception
    * @throws ProofInputException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    * @throws ProblemLoaderException Occurred Exception
    */
   protected void assertSaveAndReload(File baseDir, 
                                      String javaPathInBaseDir, 
                                      String oraclePathInBaseDirFile, 
                                      SymbolicExecutionEnvironment<?> env) throws IOException, ProofInputException, ParserConfigurationException, SAXException, ProblemLoaderException {
      File javaFile = new File(baseDir, javaPathInBaseDir);
      assertTrue(javaFile.exists());
      File tempFile = File.createTempFile("TestProgramMethodSubsetPO", ".proof", javaFile.getParentFile());
      KeYEnvironment<CustomUserInterface> reloadedEnv = null;
      SymbolicExecutionTreeBuilder reloadedBuilder = null;
      try {
         ProofSaver saver = new ProofSaver(env.getProof(), tempFile.getAbsolutePath(), Main.INTERNAL_VERSION);
         assertNull(saver.save());
         // Load proof from saved *.proof file
         reloadedEnv = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), tempFile, null, null);
         Proof reloadedProof = reloadedEnv.getLoadedProof();
         assertNotSame(env.getProof(), reloadedProof);
         // Recreate symbolic execution tree
         reloadedBuilder = new SymbolicExecutionTreeBuilder(env.getUi().getMediator(), reloadedProof, false, false, false, false);
         reloadedBuilder.analyse();
         assertSetTreeAfterStep(reloadedBuilder, oraclePathInBaseDirFile, baseDir);
      }
      finally {
         if (reloadedBuilder != null) {
            reloadedBuilder.dispose();
         }
         if (reloadedEnv != null) {
            reloadedEnv.dispose();
         }
         if (tempFile != null) {
            tempFile.delete();
            assertFalse(tempFile.exists());
         }
      }
   }
   
   /**
    * Waits until the auto mode has stopped.
    * @param ui The {@link UserInterface} to wait for.
    */
   protected void waitForAutoMode(UserInterface ui) {
      assertNotNull(ui);
      AutoModeFinishListener listener = new AutoModeFinishListener();
      ui.getMediator().addAutoModeListener(listener);
      try {
         final int TIMEOUT = 20 * 1000;
         long startTime = System.currentTimeMillis();
         while (!listener.hasAutoModeStopped()) {
            try {
               Thread.sleep(100);
               if (System.currentTimeMillis() > startTime + TIMEOUT) {
                  fail("Timeout during waiting of auto mode completed.");
               }
            }
            catch (InterruptedException e) {
            }
         }
         assertTrue(listener.hasAutoModeStopped());
      }
      finally {
         ui.getMediator().removeAutoModeListener(listener);
      }
   }
   
   /**
    * Utility class used by {@link AbstractSymbolicExecutionTestCase#waitForAutoMode(UserInterface)}.
    * @author Martin Hentschel
    */
   private static class AutoModeFinishListener implements AutoModeListener {
      /**
       * Done flag.
       */
      private boolean done = false;
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void autoModeStarted(ProofEvent e) {
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void autoModeStopped(ProofEvent e) {
         done = true;
      }

      /**
       * Checks if the auto mode has stopped.
       * @return {@code true} stopped, {@code false} still running or never started.
       */
      public boolean hasAutoModeStopped() {
         return done;
      }
   }
   
   /**
    * Executes a test with the following steps:
    * <ol>
    *    <li>Load java file</li>
    *    <li>Instantiate proof for method in container type</li>
    *    <li>Try to close proof in auto mode</li>
    *    <li>Create symbolic execution tree</li>
    *    <li>Create new oracle file in temporary directory {@link #tempNewOracleDirectory} if it is defined</li>
    *    <li>Load oracle file</li>
    *    <li>Compare created symbolic execution tree with oracle model</li>
    * </ol>
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The java class to test.
    * @param methodFullName The method to test.
    * @param precondition An optional precondition.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param includeConstraints Include constraints?
    * @param includeVariables Include variables?
    * @param includeCallStack Include call stack?
    * @param includeReturnValues Include method return values?
    * @param maximalNumberOfExecutedSetNodesPerRun The number of executed set nodes per auto mode run. The whole test is executed for each defined value.
    * @param mergeBranchConditions Merge branch conditions?
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvariants Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @throws ProofInputException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    * @throws ProblemLoaderException Occurred Exception
    */
   protected void doSETTest(File baseDir,
                            String javaPathInBaseDir,
                            String containerTypeName,
                            String methodFullName,
                            String precondition,
                            String oraclePathInBaseDirFile,
                            boolean includeConstraints,
                            boolean includeVariables,
                            boolean includeCallStack,
                            boolean includeReturnValues,
                            int[] maximalNumberOfExecutedSetNodesPerRun,
                            boolean mergeBranchConditions,
                            boolean useOperationContracts,
                            boolean useLoopInvariants,
                            boolean nonExecutionBranchHidingSideProofs,
                            boolean aliasChecks,
                            boolean useUnicode,
                            boolean usePrettyPrinting,
                            boolean variablesAreOnlyComputedFromUpdates) throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      assertNotNull(maximalNumberOfExecutedSetNodesPerRun);
      for (int i = 0; i < maximalNumberOfExecutedSetNodesPerRun.length; i++) {
         SymbolicExecutionEnvironment<CustomUserInterface> env = doSETTest(baseDir, 
                                                                           javaPathInBaseDir, 
                                                                           containerTypeName, 
                                                                           methodFullName, 
                                                                           precondition,
                                                                           oraclePathInBaseDirFile, 
                                                                           includeConstraints,
                                                                           includeVariables, 
                                                                           includeCallStack,
                                                                           includeReturnValues,
                                                                           maximalNumberOfExecutedSetNodesPerRun[i],
                                                                           mergeBranchConditions,
                                                                           useOperationContracts,
                                                                           useLoopInvariants,
                                                                           nonExecutionBranchHidingSideProofs,
                                                                           aliasChecks,
                                                                           useUnicode,
                                                                           usePrettyPrinting,
                                                                           variablesAreOnlyComputedFromUpdates);
         env.dispose();
      }
   }
   
   /**
    * Executes {@link #doSETTest(File, String, String, String, String, boolean, boolean, int, boolean, boolean, boolean)} and disposes the created {@link SymbolicExecutionEnvironment}. 
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The java class to test.
    * @param methodFullName The method to test.
    * @param precondition An optional precondition.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param includeConstraints Include constraints?
    * @param includeVariables Include variables?
    * @param includeCallStack Include call stack?
    * @param includeReturnValues Include method return values?
    * @param maximalNumberOfExecutedSetNodes The number of executed set nodes per auto mode run.
    * @param mergeBranchConditions Merge branch conditions?
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvariants Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @return The tested {@link SymbolicExecutionEnvironment}.
    * @throws ProofInputException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    * @throws ProblemLoaderException Occurred Exception
    */
   protected void doSETTestAndDispose(File baseDir,
                                      String javaPathInBaseDir,
                                      String containerTypeName,
                                      String methodFullName,
                                      String precondition,
                                      String oraclePathInBaseDirFile,
                                      boolean includeConstraints,
                                      boolean includeVariables,
                                      boolean includeCallStack,
                                      boolean includeReturnValues,
                                      int maximalNumberOfExecutedSetNodes,
                                      boolean mergeBranchConditions,
                                      boolean useOperationContracts,
                                      boolean useLoopInvariants,
                                      boolean nonExecutionBranchHidingSideProofs,
                                      boolean aliasChecks,
                                      boolean useUnicode,
                                      boolean usePrettyPrinting,
                                      boolean variablesAreOnlyComputedFromUpdates) throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      SymbolicExecutionEnvironment<CustomUserInterface> env = doSETTest(baseDir, javaPathInBaseDir, containerTypeName, methodFullName, precondition, oraclePathInBaseDirFile, includeConstraints, includeVariables, includeCallStack, includeReturnValues, maximalNumberOfExecutedSetNodes, mergeBranchConditions, useOperationContracts, useLoopInvariants, nonExecutionBranchHidingSideProofs, aliasChecks, useUnicode, usePrettyPrinting, variablesAreOnlyComputedFromUpdates);
      env.dispose();
   }

   /**
    * Executes a test with the following steps:
    * <ol>
    *    <li>Load java file</li>
    *    <li>Instantiate proof for method in container type</li>
    *    <li>Try to close proof in auto mode</li>
    *    <li>Create symbolic execution tree</li>
    *    <li>Create new oracle file in temporary directory {@link #tempNewOracleDirectory} if it is defined</li>
    *    <li>Load oracle file</li>
    *    <li>Compare created symbolic execution tree with oracle model</li>
    * </ol>
    * @param baseDir The base directory which contains test and oracle file.
    * @param proofFilePathInBaseDir The path to the proof file inside the base directory.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param includeConstraints Include constraints?
    * @param includeVariables Include variables?
    * @param includeCallStack Include call stack?
    * @param includeReturnValues Include method return values?
    * @param mergeBranchConditions Merge branch conditions?
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvariants Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @return The tested {@link SymbolicExecutionEnvironment}.
    * @throws ProofInputException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    * @throws ProblemLoaderException Occurred Exception
    */
   protected void doSETTest(File baseDir,
                            String proofFilePathInBaseDir,
                            String oraclePathInBaseDirFile,
                            boolean includeConstraints,
                            boolean includeVariables,
                            boolean includeCallStack,
                            boolean includeReturnValues,
                            boolean mergeBranchConditions,
                            boolean useOperationContracts,
                            boolean useLoopInvariants,
                            boolean nonExecutionBranchHidingSideProofs,
                            boolean aliasChecks,
                            boolean useUnicode,
                            boolean usePrettyPrinting,
                            boolean variablesAreOnlyComputedFromUpdates) throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      SymbolicExecutionEnvironment<CustomUserInterface> env = null;
      try {
         // Make sure that parameter are valid.
         assertNotNull(proofFilePathInBaseDir);
         assertNotNull(oraclePathInBaseDirFile);
         File oracleFile = new File(baseDir, oraclePathInBaseDirFile);
         if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            assertTrue("Oracle file does not exist. Set \"CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY\" to true to create an oracle file.", oracleFile.exists());
         }
         // Make sure that the correct taclet options are defined.
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(baseDir, proofFilePathInBaseDir, mergeBranchConditions, useOperationContracts, useLoopInvariants, nonExecutionBranchHidingSideProofs, aliasChecks, useUnicode, usePrettyPrinting, variablesAreOnlyComputedFromUpdates);
         // Create new oracle file if required in a temporary directory
         createOracleFile(env.getBuilder().getStartNode(), oraclePathInBaseDirFile, includeConstraints, includeVariables, includeCallStack, includeReturnValues);
         // Read oracle file
         ExecutionNodeReader reader = new ExecutionNodeReader();
         IExecutionNode<?> oracleRoot = reader.read(oracleFile);
         assertNotNull(oracleRoot);
         // Make sure that the created symbolic execution tree matches the expected one.
         assertExecutionNodes(oracleRoot, env.getBuilder().getStartNode(), includeVariables, includeCallStack, false, includeReturnValues, includeConstraints);
      }
      finally {
         // Restore original options
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         if (env != null) {
            env.dispose();
         }
      }
   }
   
   /**
    * Executes a test with the following steps:
    * <ol>
    *    <li>Load java file</li>
    *    <li>Instantiate proof for method in container type</li>
    *    <li>Try to close proof in auto mode</li>
    *    <li>Create symbolic execution tree</li>
    *    <li>Create new oracle file in temporary directory {@link #tempNewOracleDirectory} if it is defined</li>
    *    <li>Load oracle file</li>
    *    <li>Compare created symbolic execution tree with oracle model</li>
    * </ol>
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The java class to test.
    * @param methodFullName The method to test.
    * @param precondition An optional precondition.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param includeConstraints Include constraints?
    * @param includeVariables Include variables?
    * @param includeCallStack Include call stack?
    * @param includeReturnValues Include method return values?
    * @param maximalNumberOfExecutedSetNodes The number of executed set nodes per auto mode run.
    * @param mergeBranchConditions Merge branch conditions?
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvariants Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @return The tested {@link SymbolicExecutionEnvironment}.
    * @throws ProofInputException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    * @throws ProblemLoaderException Occurred Exception
    */
   protected SymbolicExecutionEnvironment<CustomUserInterface> doSETTest(File baseDir,
                                                                                String javaPathInBaseDir,
                                                                                String containerTypeName,
                                                                                final String methodFullName,
                                                                                String precondition,
                                                                                String oraclePathInBaseDirFile,
                                                                                boolean includeConstraints,
                                                                                boolean includeVariables,
                                                                                boolean includeCallStack,
                                                                                boolean includeReturnValues,
                                                                                int maximalNumberOfExecutedSetNodes,
                                                                                boolean mergeBranchConditions,
                                                                                boolean useOperationContracts,
                                                                                boolean useLoopInvariants,
                                                                                boolean nonExecutionBranchHidingSideProofs,
                                                                                boolean aliasChecks,
                                                                                boolean useUnicode,
                                                                                boolean usePrettyPrinting,
                                                                                boolean variablesAreOnlyComputedFromUpdates) throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         // Make sure that parameter are valid.
         assertNotNull(javaPathInBaseDir);
         assertNotNull(containerTypeName);
         assertNotNull(methodFullName);
         assertNotNull(oraclePathInBaseDirFile);
         File oracleFile = new File(baseDir, oraclePathInBaseDirFile);
         if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            assertTrue("Oracle file does not exist. Set \"CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY\" to true to create an oracle file.", oracleFile.exists());
         }
         assertTrue(maximalNumberOfExecutedSetNodes >= 1);
         // Make sure that the correct taclet options are defined.
         originalTacletOptions = setDefaultTacletOptions(baseDir, javaPathInBaseDir, containerTypeName, methodFullName);
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         SymbolicExecutionEnvironment<CustomUserInterface> env = createSymbolicExecutionEnvironment(baseDir, javaPathInBaseDir, containerTypeName, methodFullName, precondition, mergeBranchConditions, useOperationContracts, useLoopInvariants, nonExecutionBranchHidingSideProofs, aliasChecks, useUnicode, usePrettyPrinting, variablesAreOnlyComputedFromUpdates);
         internalDoSETTest(oracleFile, env, oraclePathInBaseDirFile, maximalNumberOfExecutedSetNodes, includeConstraints, includeVariables, includeCallStack, includeReturnValues);
         return env;
      }
      finally {
         // Restore original options
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         restoreTacletOptions(originalTacletOptions);
      }
   }
   
   /**
    * Executes a test with the following steps:
    * <ol>
    *    <li>Load java file</li>
    *    <li>Instantiate proof for method in container type</li>
    *    <li>Try to close proof in auto mode</li>
    *    <li>Create symbolic execution tree</li>
    *    <li>Create new oracle file in temporary directory {@link #tempNewOracleDirectory} if it is defined</li>
    *    <li>Load oracle file</li>
    *    <li>Compare created symbolic execution tree with oracle model</li>
    * </ol>
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param baseContractName The name of the contract.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param includeConstraints Include constraints?
    * @param includeVariables Include variables?
    * @param includeCallStack Include call stack?
    * @param includeReturnValues Include method return values?
    * @param maximalNumberOfExecutedSetNodes The number of executed set nodes per auto mode run.
    * @param mergeBranchConditions Merge branch conditions?
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvariants Use loop invariants?
    * @param nonExecutionBranchHidingSideProofs {@code true} hide non execution branch labels by side proofs, {@code false} do not hide execution branch labels. 
    * @param aliasChecks Do alias checks?
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    * @param variablesAreOnlyComputedFromUpdates {@code true} {@link IExecutionVariable} are only computed from updates, {@code false} {@link IExecutionVariable}s are computed according to the type structure of the visible memory.
    * @return The tested {@link SymbolicExecutionEnvironment}.
    * @throws ProofInputException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    * @throws ProblemLoaderException Occurred Exception
    */
   protected SymbolicExecutionEnvironment<CustomUserInterface> doSETTest(File baseDir,
                                                                                String javaPathInBaseDir,
                                                                                String baseContractName,
                                                                                String oraclePathInBaseDirFile,
                                                                                boolean includeConstraints,
                                                                                boolean includeVariables,
                                                                                boolean includeCallStack,
                                                                                boolean includeReturnValues,
                                                                                int maximalNumberOfExecutedSetNodes,
                                                                                boolean mergeBranchConditions,
                                                                                boolean useOperationContracts,
                                                                                boolean useLoopInvariants,
                                                                                boolean nonExecutionBranchHidingSideProofs,
                                                                                boolean aliasChecks,
                                                                                boolean useUnicode,
                                                                                boolean usePrettyPrinting,
                                                                                boolean variablesAreOnlyComputedFromUpdates) throws ProofInputException, IOException, ParserConfigurationException, SAXException, ProblemLoaderException {
      HashMap<String, String> originalTacletOptions = null;
      try {
         // Make sure that parameter are valid.
         assertNotNull(javaPathInBaseDir);
         assertNotNull(baseContractName);
         assertNotNull(oraclePathInBaseDirFile);
         File oracleFile = new File(baseDir, oraclePathInBaseDirFile);
         if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            assertTrue("Oracle file does not exist. Set \"CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY\" to true to create an oracle file.", oracleFile.exists());
         }
         assertTrue(maximalNumberOfExecutedSetNodes >= 1);
         // Make sure that the correct taclet options are defined.
         originalTacletOptions = setDefaultTacletOptions(baseDir, javaPathInBaseDir, baseContractName);
         // Create proof environment for symbolic execution
         SymbolicExecutionEnvironment<CustomUserInterface> env = createSymbolicExecutionEnvironment(baseDir, javaPathInBaseDir, baseContractName, mergeBranchConditions, useOperationContracts, useLoopInvariants, nonExecutionBranchHidingSideProofs, aliasChecks, useUnicode, usePrettyPrinting, variablesAreOnlyComputedFromUpdates);
         internalDoSETTest(oracleFile, env, oraclePathInBaseDirFile, maximalNumberOfExecutedSetNodes, includeConstraints, includeVariables, includeCallStack, includeReturnValues);
         return env;
      }
      finally {
         // Restore taclet options
         restoreTacletOptions(originalTacletOptions);
      }
   }

   /**
    * Internal test method called by
    * {@link #doSETTest(File, String, String, String, boolean, boolean, boolean, int, boolean, boolean, boolean, boolean, boolean)} and
    * {@link #doSETTest(File, String, String, String, String, String, boolean, boolean, boolean, int, boolean, boolean, boolean, boolean, boolean)}.
    */
   private void internalDoSETTest(File oracleFile, SymbolicExecutionEnvironment<CustomUserInterface> env, String oraclePathInBaseDirFile, int maximalNumberOfExecutedSetNodes, boolean includeConstraints, boolean includeVariables, boolean includeCallStack, boolean includeReturnValues) throws IOException, ProofInputException, ParserConfigurationException, SAXException {
      // Set stop condition to stop after a number of detected symbolic execution tree nodes instead of applied rules
      ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = new ExecutedSymbolicExecutionTreeNodesStopCondition(maximalNumberOfExecutedSetNodes);
      env.getProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      int nodeCount;
      // Execute auto mode until no more symbolic execution tree nodes are found or no new rules are applied.
      do {
         // Store the number of nodes before start of the auto mode 
         nodeCount = env.getProof().countNodes();
         // Run proof
         env.getUi().startAndWaitForAutoMode(env.getProof());
         // Update symbolic execution tree 
         env.getBuilder().analyse();
         // Make sure that not to many set nodes are executed
         Map<Goal, Integer> executedSetNodesPerGoal = stopCondition.getExectuedSetNodesPerGoal();
         for (Integer value : executedSetNodesPerGoal.values()) {
            assertNotNull(value);
            assertTrue(value.intValue() + " is not less equal to " + maximalNumberOfExecutedSetNodes, value.intValue() <= maximalNumberOfExecutedSetNodes);
         }
      } while(stopCondition.wasSetNodeExecuted() && nodeCount != env.getProof().countNodes());
      // Create new oracle file if required in a temporary directory
      createOracleFile(env.getBuilder().getStartNode(), oraclePathInBaseDirFile, includeConstraints, includeVariables, includeCallStack, includeReturnValues);
      // Read oracle file
      ExecutionNodeReader reader = new ExecutionNodeReader();
      IExecutionNode<?> oracleRoot = reader.read(oracleFile);
      assertNotNull(oracleRoot);
      // Make sure that the created symbolic execution tree matches the expected one.
      assertExecutionNodes(oracleRoot, env.getBuilder().getStartNode(), includeVariables, includeCallStack, false, includeReturnValues, includeConstraints);
   }
   
   /**
    * Ensures that the default taclet options are defined.
    * @param baseDir The base directory which contains the java file.
    * @param javaPathInBaseDir The path in the base directory to the java file.
    * @param baseContractName The name of the contract to prove.
    * @return The original settings which are overwritten.
    * @throws ProblemLoaderException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   public static HashMap<String, String> setDefaultTacletOptions(File baseDir,
                                                                 String javaPathInBaseDir,
                                                                 String baseContractName) throws ProblemLoaderException, ProofInputException {
      if (!SymbolicExecutionUtil.isChoiceSettingInitialised()) {
         SymbolicExecutionEnvironment<CustomUserInterface> env = createSymbolicExecutionEnvironment(keyRepDirectory, javaPathInBaseDir, baseContractName, false, false, false, false, false, false, false, false);
         env.dispose();
      }
      return setDefaultTacletOptions();
   }

   /**
    * Ensures that the default taclet options are defined.
    * @param baseDir The base directory which contains the java file.
    * @param javaPathInBaseDir The path in the base directory to the java file.
    * @param containerTypeName The type nach which provides the method.
    * @param methodFullName The method to prove.
    * @return The original settings which are overwritten.
    * @throws ProblemLoaderException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   public static HashMap<String, String> setDefaultTacletOptions(File baseDir,
                                                                 String javaPathInBaseDir,
                                                                 String containerTypeName,
                                                                 String methodFullName) throws ProblemLoaderException, ProofInputException {
      if (!SymbolicExecutionUtil.isChoiceSettingInitialised()) {
         SymbolicExecutionEnvironment<CustomUserInterface> env = createSymbolicExecutionEnvironment(baseDir, javaPathInBaseDir, containerTypeName, methodFullName, null, false, false, false, false, false, false, false, false);
         env.dispose();
      }
      return setDefaultTacletOptions();
   }

   /**
    * Ensures that the default taclet options are defined.
    * @param javaFile The java file to load.
    * @param containerTypeName The type name which provides the target.
    * @param targetName The target to proof.
    * @return The original settings which are overwritten.
    * @throws ProblemLoaderException Occurred Exception.
    * @throws ProofInputException Occurred Exception.
    */
   public static HashMap<String, String> setDefaultTacletOptionsForTarget(File javaFile,
                                                                          String containerTypeName,
                                                                          final String targetName) throws ProblemLoaderException, ProofInputException {
      if (!SymbolicExecutionUtil.isChoiceSettingInitialised()) {
         KeYEnvironment<?> environment = null;
         Proof proof = null;
         try {
            // Load java file
            environment = KeYEnvironment.load(javaFile, null, null);
            // Search type
            KeYJavaType containerKJT = environment.getJavaInfo().
                    getTypeByClassName(containerTypeName);
            assertNotNull(containerKJT);
            // Search observer function
            ImmutableSet<IObserverFunction> targets = environment.getSpecificationRepository().getContractTargets(containerKJT);
            IObserverFunction target = JavaUtil.search(targets, new IFilter<IObserverFunction>() {
               @Override
               public boolean select(IObserverFunction element) {
                  return targetName.equals(element.toString());
               }
            });
            assertNotNull(target);
            // Find first contract.
            ImmutableSet<Contract> contracts = environment.getSpecificationRepository().getContracts(containerKJT, target);
            assertFalse(contracts.isEmpty());
            Contract contract = contracts.iterator().next();
            // Start proof
            proof = environment.createProof(contract.createProofObl(environment.getInitConfig(), contract));
            assertNotNull(proof);
         }
         catch (Exception e) {
            if (proof != null) {
               proof.dispose();
            }
            if (environment != null) {
               environment.dispose();
            }
         }
      }
      return setDefaultTacletOptions();
   }

   /**
    * Ensures that the default taclet options are defined.
    * @return The original settings which are overwritten.
    */
   public static HashMap<String, String> setDefaultTacletOptions() {
      assertTrue(SymbolicExecutionUtil.isChoiceSettingInitialised());
      // Set default taclet options
      ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
      HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
      HashMap<String, String> newSettings = new HashMap<String, String>(oldSettings);
      newSettings.putAll(SymbolicExecutionUtil.getDefaultTacletOptions());
      choiceSettings.setDefaultChoices(newSettings);
      // Make sure that default taclet options are set
      HashMap<String, String> updatedChoiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
      for (Entry<String, String> entry : newSettings.entrySet()) {
         assertEquals(entry.getValue(), updatedChoiceSettings.get(entry.getKey()));
      }
      return oldSettings;
   }

   /**
    * Restores the given taclet options.
    * @param options The taclet options to restore.
    */
   public static void restoreTacletOptions(HashMap<String, String> options) {
      if (options != null) {
         assertTrue(SymbolicExecutionUtil.isChoiceSettingInitialised());
         ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(options);
         // Make sure that taclet options are restored
         HashMap<String, String> updatedChoiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
         for (Entry<String, String> entry : options.entrySet()) {
            assertEquals(entry.getValue(), updatedChoiceSettings.get(entry.getKey()));
         }
      }
   }

   /**
    * creates a new factory that should be used by others afterwards
    * @return 
    */
   protected ITermProgramVariableCollectorFactory createNewProgramVariableCollectorFactory(final SymbolicExecutionBreakpointStopCondition breakpointParentStopCondition) {
      ITermProgramVariableCollectorFactory programVariableCollectorFactory = new ITermProgramVariableCollectorFactory() {
         @Override
         public TermProgramVariableCollector create(Services services) {
            return new TermProgramVariableCollectorKeepUpdatesForBreakpointconditions(services, breakpointParentStopCondition);
         }
      };
      return programVariableCollectorFactory;
   }

      /**
    * Makes sure that two {@link Term}s are equal.
    * @param expected The expected {@link Term}.
    * @param actual The actual {@link Term}.
    */
   protected void assertTerm(Term expected, Term actual) {
      if (expected != null) {
         assertEquals(expected.op(), actual.op());
         assertEquals(expected.javaBlock(), actual.javaBlock());
         assertEquals(expected.getLabels(), actual.getLabels());
         assertEquals(expected.arity(), actual.arity());
         for (int i = 0; i < expected.arity(); i++) {
            assertTerm(expected.sub(i), actual.sub(i));
         }
      }
      else {
         assertNull(actual);
      }
   }

   /**
    * Checks if one step simplification is enabled in the given {@link Proof}.
    * @param proof The {@link Proof} to read from or {@code null} to return the general settings value.
    * @return {@code true} one step simplification is enabled, {@code false} if disabled.
    */
   public static boolean isOneStepSimplificationEnabled(Proof proof) {
      if (proof != null && !proof.isDisposed()) {
         return proof.getProofIndependentSettings().getGeneralSettings().oneStepSimplification();
      }
      else {
         return ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().oneStepSimplification();
      }
   }

   /**
    * Defines if one step simplification is enabled in general and within the {@link Proof}.
    * @param proof The optional {@link Proof}.
    * @param enabled {@code true} use one step simplification, {@code false} do not use one step simplification.
    */
   public static void setOneStepSimplificationEnabled(Proof proof, boolean enabled) {
      ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(enabled);
      if (proof != null && !proof.isDisposed()) {
         proof.getProofIndependentSettings().getGeneralSettings().setOneStepSimplification(enabled);
         OneStepSimplifier simplifier = MiscTools.findOneStepSimplifier(proof.getServices().getProfile());
         if (simplifier != null) {
            simplifier.refresh(proof);
         }
      }
   }
}
