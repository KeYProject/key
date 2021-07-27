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

package de.uka.ilkd.key.util;

import junit.framework.TestCase;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;

/**
 * Tests for {@link SearchNodePreorderIterator}.
 * @author Martin Hentschel
 */
public class TestSearchNodePreorderIterator extends TestCase {
   /**
    * Tests a tree of {@link Node}s with three levels after root.
    */
   public void testNodesThreeLevel() {
      // Create tree to test
      Proof proof = new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Node root = appendRoot(proof);
      Node l1 = appendNode(proof, root);
      Node l11 = appendNode(proof, l1);
      appendNode(proof, l11);
      appendNode(proof, l1);
      Node l2 = appendNode(proof, root);
      appendNode(proof, l2);
      Node l22 = appendNode(proof, l2);
      appendNode(proof, l22);
      appendNode(proof, l22);
      appendNode(proof, l2);
      appendNode(proof, root);
      Node l4 = appendNode(proof, root);
      appendNode(proof, l4);
      // Test tree
      assertRoot(root);
   }
   
   /**
    * Tests a tree of {@link Node}s with two levels after root.
    */
   public void testNodesTwoLevel() {
      // Create tree to test
      Proof proof = new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Node root = appendRoot(proof);
      Node l1 = appendNode(proof, root);
      appendNode(proof, l1);
      appendNode(proof, l1);
      Node l2 = appendNode(proof, root);
      appendNode(proof, l2);
      appendNode(proof, l2);
      appendNode(proof, l2);
      appendNode(proof, root);
      Node l4 = appendNode(proof, root);
      appendNode(proof, l4);
      // Test tree
      assertRoot(root);
   }
   
   /**
    * Tests a tree of {@link Node}s with one level after root.
    */
   public void testNodesOneLevel() {
      // Create tree to test
      Proof proof = new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Node root = appendRoot(proof);
      appendNode(proof, root);
      appendNode(proof, root);
      appendNode(proof, root);
      appendNode(proof, root);
      // Test tree
      assertRoot(root);
   }
   
   /**
    * Tests only a root {@link Node}.
    */
   public void testEmptyRoot() {
      // Create tree to test
      Proof proof = new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
      Node root = appendRoot(proof);
      // Test tree
      assertRoot(root);
   }
   
   /**
    * Starts at all {@link Node}s of the given proof tree a traversal.
    * @param root The root of the proof tree.
    */
   protected void assertRoot(Node root) {
      // List children
      NodePreorderIterator iter = new NodePreorderIterator(root);
      ImmutableList<Node> childList = ImmutableSLList.<Node>nil();
      while (iter.hasNext()) {
         Node next = iter.next();
         childList = childList.append(next);
      }
      // Test each child
      while (!childList.isEmpty()) {
         assertPreorder(childList.head(), childList);
         childList = childList.take(1);
      }
   }
   
   /**
    * Tests a iteration starting at the given {@link Node}.
    * @param start The {@link Node} to start iteration.
    * @param expectedChildList The expected previous {@link Node}s.
    */
   protected void assertPreorder(Node start, ImmutableList<Node> expectedChildList) {
      SearchNodePreorderIterator iter = new SearchNodePreorderIterator(start);
      assertTrue(iter.hasNext());
      while (iter.hasNext()) {
         Node previous = iter.next();
         assertEquals(previous, expectedChildList.head());
         expectedChildList = expectedChildList.take(1); // Remove head
      }
      assertTrue("Child list still contains " + expectedChildList.size() + " elements.", expectedChildList.isEmpty());
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