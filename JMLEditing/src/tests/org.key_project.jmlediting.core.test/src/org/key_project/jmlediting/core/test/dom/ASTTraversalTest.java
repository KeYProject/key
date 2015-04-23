package org.key_project.jmlediting.core.test.dom;

import static org.junit.Assert.assertEquals;
import static org.key_project.jmlediting.core.test.utilities.ASTTestUtils.*;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.test.utilities.ASTTestUtils;

public class ASTTraversalTest {

   @Test
   public void testTraversal1() {
      final List<Integer> traversalResult = ASTTestUtils.NODE_1.traverse(
            new INodeTraverser<List<Integer>>() {

               @Override
               public List<Integer> traverse(final IASTNode node,
                     final List<Integer> existing) {
                  existing.add(node.getType());
                  return existing;
               }
            }, new LinkedList<Integer>());
      assertEquals("Traversal missed a node", 7, traversalResult.size());
      assertEquals("Traversal order not correct",
            Arrays.asList(T3, T5, T4, T1, T6, T2, T0), traversalResult);
   }

   @Test
   public void testTraversal2() {
      final Integer traversalResult = ASTTestUtils.NODE_2.traverse(
            new INodeTraverser<Integer>() {

               @Override
               public Integer traverse(final IASTNode node,
                     final Integer existing) {
                  return existing + 1;
               }
            }, 0);
      assertEquals("Missed the node", (Integer) 1, traversalResult);
   }

   @Test
   public void testTraversal3() {
      final String traversalResult = ASTTestUtils.NODE_3.traverse(
            new INodeTraverser<String>() {

               @Override
               public String traverse(final IASTNode node, final String existing) {
                  if (Nodes.isString(node)) {
                     return existing + ((IStringNode) node).getString();
                  }
                  return existing;
               }
            }, "");
      assertEquals("Order of nodes is not correct", "123456", traversalResult);
   }

}
