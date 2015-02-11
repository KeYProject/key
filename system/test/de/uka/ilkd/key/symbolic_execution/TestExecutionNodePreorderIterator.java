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

import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.AbstractKeYlessExecutionNode;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessStart;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodeReader.KeYlessStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.impl.TreeSettings;
import de.uka.ilkd.key.ui.CustomUserInterface;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * Tests for {@link ExecutionNodePreorderIterator}.
 * @author Martin Hentschel
 */
public class TestExecutionNodePreorderIterator extends TestCase {
   /**
    * Tests a tree of {@link IExecutionNode}s with three levels after root.
    */
   public void testNodesThreeLevel() throws ProofInputException {
      // Create tree to test
      Proof proof = new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Node root = appendRoot(proof);
      Node l1 = appendNode(proof, root);
      Node l11 = appendNode(proof, l1);
      Node l111 = appendNode(proof, l11);
      Node l12 = appendNode(proof, l1);
      Node l2 = appendNode(proof, root);
      Node l21 = appendNode(proof, l2);
      Node l22 = appendNode(proof, l2);
      Node l221 = appendNode(proof, l22);
      Node l222 = appendNode(proof, l22);
      Node l23 = appendNode(proof, l2);
      Node l3 = appendNode(proof, root);
      Node l4 = appendNode(proof, root);
      Node l41 = appendNode(proof, l4);
      // Create execution test model
      KeYlessStart executionRoot = new KeYlessStart("<start>", null, false);
      KeYlessStatement el1 = createStatement(executionRoot, l1);
      KeYlessStatement el11 = createStatement(el1, l11);
      createStatement(el11, l111);
      createStatement(el1, l12);
      KeYlessStatement el2 = createStatement(executionRoot, l2);
      createStatement(el2, l21);
      KeYlessStatement el22 = createStatement(el2, l22);
      createStatement(el22, l221);
      createStatement(el22, l222);
      createStatement(el2, l23);
      createStatement(executionRoot, l3);
      KeYlessStatement el4 = createStatement(executionRoot, l4);
      createStatement(el4, l41);
      // Test tree
      ExpectedNode[] level111 = createExpectedNodes("3");
      ExpectedNode[] level11 = createExpectedNodes(new String[] {"2", "4"}, level111, null);
      ExpectedNode[] level122 = createExpectedNodes("8", "9");
      ExpectedNode[] level12 = createExpectedNodes(new String[] {"6", "7", "10"}, null, level122, null);
      ExpectedNode[] level14 = createExpectedNodes("13");
      ExpectedNode[] level1 = createExpectedNodes(new String[] {"1", "5", "11", "12"}, level11, level12, null, level14);
      assertRoot(executionRoot, createExpectedNodes(new String[] {"<start>"}, level1));
   }
   
   /**
    * Tests a tree of {@link IExecutionNode}s with two levels after root.
    */
   public void testNodesTwoLevel() throws ProofInputException {
      // Create tree to test
      Proof proof = new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Node root = appendRoot(proof);
      Node l1 = appendNode(proof, root);
      Node l11 = appendNode(proof, l1);
      Node l12 = appendNode(proof, l1);
      Node l2 = appendNode(proof, root);
      Node l21 = appendNode(proof, l2);
      Node l22 = appendNode(proof, l2);
      Node l23 = appendNode(proof, l2);
      Node l3 = appendNode(proof, root);
      Node l4 = appendNode(proof, root);
      Node l41 = appendNode(proof, l4);
      // Create execution test model
      KeYlessStart executionRoot = new KeYlessStart("<start>", null, false);
      KeYlessStatement el1 = createStatement(executionRoot, l1);
      createStatement(el1, l11);
      createStatement(el1, l12);
      KeYlessStatement el2 = createStatement(executionRoot, l2);
      createStatement(el2, l21);
      createStatement(el2, l22);
      createStatement(el2, l23);
      createStatement(executionRoot, l3);
      KeYlessStatement el4 = createStatement(executionRoot, l4);
      createStatement(el4, l41);
      // Test tree
      ExpectedNode[] level11 = createExpectedNodes("2", "3");
      ExpectedNode[] level12 = createExpectedNodes("5", "6", "7");
      ExpectedNode[] level14 = createExpectedNodes("10");
      ExpectedNode[] level1 = createExpectedNodes(new String[] {"1", "4", "8", "9"}, level11, level12, null, level14);
      assertRoot(executionRoot, createExpectedNodes(new String[] {"<start>"}, level1));
   }
   
   /**
    * Tests a tree of {@link IExecutionNode}s with one level after root.
    */
   public void testNodesOneLevel() throws ProofInputException {
      // Create tree to test
      Proof proof = new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Node root = appendRoot(proof);
      Node child1 = appendNode(proof, root);
      Node child2 = appendNode(proof, root);
      Node child3 = appendNode(proof, root);
      Node child4 = appendNode(proof, root);
      // Create execution test model
      KeYlessStart executionRoot = new KeYlessStart("<start>", null, false);
      createStatement(executionRoot, child1);
      createStatement(executionRoot, child2);
      createStatement(executionRoot, child3);
      createStatement(executionRoot, child4);
      // Test tree
      ExpectedNode[] level1 = createExpectedNodes("1", "2", "3", "4");
      assertRoot(executionRoot, createExpectedNodes(new String[] {"<start>"}, level1));
   }
   
   /**
    * Creates a new {@link KeYlessStatement} which represents the given {@link Node} in KeY's proof tree.
    * @param parent The parent {@link AbstractKeYlessExecutionNode}.
    * @param proofNode The {@link Node} in KeY's proof tree to represent.
    * @return The created {@link KeYlessStatement}.
    */
   protected KeYlessStatement createStatement(AbstractKeYlessExecutionNode<?> parent, Node proofNode) {
      KeYlessStatement statement = new KeYlessStatement(parent, proofNode.serialNr() + "", null, false);
      parent.addChild(statement);
      return statement;
   }

   /**
    * Tests only a root {@link IExecutionNode}.
    */
   public void testEmptyRoot() throws ProofInputException {
      // Create tree to test
      UserInterface ui = new CustomUserInterface(false);
      KeYMediator mediator = new KeYMediator(ui);
      Proof proof = new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Node root = appendRoot(proof);
      // Create execution test model
      TreeSettings settings = new TreeSettings(false, false, false, false);
      ExecutionStart executionRoot = new ExecutionStart(settings, mediator, root);
      // Test tree
      assertRoot(executionRoot, createExpectedNodes("<start>"));
   }
   
   /**
    * Makes sure that a {@link ExecutionNodePreorderIterator} which iterates over the given
    * {@link IExecutionNode} returns nodes in preorder iteration over the
    * expected trees.
    * @param element The {@link IExecutionNode} to iterate over.
    * @param expectedRoots The expected values.
    * @throws ProofInputException Occurred Exception. 
    */
   protected void assertRoot(IExecutionNode<?> element, 
                             ExpectedNode[] expectedRoots) throws ProofInputException {
      ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(element);
      assertExpectedNodes(iter, expectedRoots, false);
      assertFalse(iter.hasNext());
   }
   
   /**
    * Makes sure that the nodes returned by the given {@link ExecutionNodePreorderIterator}
    * are equal to the defined model.
    * @param iter The {@link ExecutionNodePreorderIterator} to test.
    * @param expectedRoots The expected model.
    * @param iterateOverSubtree Start new sub tree iteration at the current node?
    * @throws ProofInputException Occurred Exception.
    */
   protected void assertExpectedNodes(ExecutionNodePreorderIterator iter, 
                                      ExpectedNode[] expectedRoots,
                                      boolean iterateOverSubtree) throws ProofInputException {
      if (expectedRoots != null) {
         assertNotNull(iter);
         for (ExpectedNode node : expectedRoots) {
            assertTrue(iter.hasNext());
            IExecutionNode<?> next = iter.next();
            assertNotNull(next);
            assertEquals(node.getExpectedName(), next.getName());
            if (iterateOverSubtree) {
               assertRoot(next, new ExpectedNode[] {node});
            }
            assertExpectedNodes(iter, node.getExpectedChildren(), true);
         }
      }
   }
   
   /**
    * Forms the expected tree.
    * @author Martin Hentschel
    */
   protected static class ExpectedNode {
      /**
       * The expected name.
       */
      private String expectedName;
      
      /**
       * The expected children.
       */
      private ExpectedNode[] expectedChildren;

      /**
       * Constructor.
       * @param expectedName The expected name.
       */
      public ExpectedNode(String expectedName) {
         this.expectedName = expectedName;
      }

      /**
       * Constructor.
       * @param expectedName The expected name.
       * @param expectedChildren The expected children.
       */
      public ExpectedNode(String expectedName, ExpectedNode[] expectedChildren) {
         this.expectedName = expectedName;
         this.expectedChildren = expectedChildren;
      }
      
      /**
       * Returns the expected name.
       * @return The expected name.
       */
      public String getExpectedName() {
         return expectedName;
      }

      /**
       * Returns the expected children.
       * @return The expected children.
       */
      public ExpectedNode[] getExpectedChildren() {
         return expectedChildren;
      }
   }

   /**
    * Creates new {@link ExpectedNode}s with the given names and children.
    * @param expectedNames The given names.
    * @param children The given children.
    * @return The created {@link ExpectedNode}s.
    */
   protected ExpectedNode[] createExpectedNodes(String[] expectedNames, ExpectedNode[]... children) {
      assertEquals(expectedNames.length, children.length);
      List<ExpectedNode> result = new LinkedList<ExpectedNode>();
      for (int i = 0; i < expectedNames.length; i++) {
         result.add(new ExpectedNode(expectedNames[i], children[i]));
      }
      return result.toArray(new ExpectedNode[result.size()]);
   }
   
   /**
    * Creates new {@link ExpectedNode}s with the given names.
    * @param expectedNames The given names.
    * @return The created {@link ExpectedNode}s.
    */
   protected ExpectedNode[] createExpectedNodes(String... expectedNames) {
      List<ExpectedNode> result = new LinkedList<ExpectedNode>();
      for (String name : expectedNames) {
         result.add(new ExpectedNode(name));
      }
      return result.toArray(new ExpectedNode[result.size()]);
   }
   
   /**
    * Appends a new node to the given parent {@link Node}.
    * @param proof The {@link Proof} which forms the test model.
    * @param parent The parent {@link Node} to add to.
    * @return The new created child {@link Node}.
    */
   protected Node appendNode(Proof proof, Node parent) {
      Node newChild = new Node(proof);
      parent.add(newChild);
      return newChild;
   }
   
   /**
    * Sets a new root {@link Node} on the proof.
    * @param proof The {@link Proof} to set root on.
    * @return The created root {@link Node}.
    */
   protected Node appendRoot(Proof proof) {
      Node root = new Node(proof);
      proof.setRoot(root);
      return root;
   }
}