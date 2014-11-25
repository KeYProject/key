package org.key_project.jmlediting.core.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IBehaviorSpecification;
import org.key_project.jmlediting.core.dom.ILightweightSpecification;
import org.key_project.jmlediting.core.dom.IMethodSpecification;
import org.key_project.jmlediting.core.dom.ISpecificationCase;
import org.key_project.jmlediting.core.dom.ISpecificationStatement;
import org.key_project.jmlediting.core.dom.NodeTypes;

public class DomCompareUtils {
   
   public static void equalsASTNode(IASTNode n1, IASTNode n2, boolean ignoreOffsets) {
      if (ignoreOffsets) {
         assertEquals("Start offset not equal", n1.getStartOffset(), n2.getStartOffset());
         assertEquals("End offset not equal", n1.getEndOffset(), n2.getEndOffset());
      }
   }
   
   public static void equalsSpecificationStatements(ISpecificationStatement s1, ISpecificationStatement s2, boolean ignoreOffsets) {
      equalsASTNode(s1, s2, ignoreOffsets);
      assertEquals("Specification keyword not equal", s1.getKeyword(), s2.getKeyword());
      assertEquals("Content not equal", s1.getContent(), s2.getContent());
   }
   
   public static void equalsBehaviorSpecification(IBehaviorSpecification b1, IBehaviorSpecification b2, boolean ignoreOffsets) {
      equalsASTNode(b1, b2, ignoreOffsets);
      assertEquals("Specification keyword not equal", b1.getKeyword(), b2.getKeyword());
      assertEquals("Number of Specifications not equal", b1.getSpecificationStatements().size(), b2.getSpecificationStatements().size());
      for (int i = 0; i < b1.getSpecificationStatements().size(); i++) {
         equalsSpecificationStatements(b1.getSpecificationStatements().get(i), b2.getSpecificationStatements().get(i), ignoreOffsets);
      }
   }
   
   public static void equalsLightWeightSpecification(ILightweightSpecification l1, ILightweightSpecification l2, boolean ignoreOffsets) {
      equalsASTNode(l1, l2, ignoreOffsets);
      assertEquals("Number of specifications not equal", l1.getSpecificationStatements().size(), l2.getSpecificationStatements().size());
      for (int i = 0; i < l1.getSpecificationStatements().size(); i++) {
         equalsSpecificationStatements(l1.getSpecificationStatements().get(i), l2.getSpecificationStatements().get(i), ignoreOffsets);
      }
   }
   
   public static void equalsMethodSpecification(IMethodSpecification m1, IMethodSpecification m2, boolean ignoreOffsets) {
      equalsASTNode(m1, m2, ignoreOffsets);
      assertEquals("Extending specification not equal", m1.isExtendingSpecification(), m2.isExtendingSpecification());
      assertEquals("Number of Specification Cases not equal", m1.getSpecificationCases().size(), m2.getSpecificationCases().size());
      for (int i = 0; i < m1.getSpecificationCases().size(); i++) {
         ISpecificationCase c1 = m1.getSpecificationCases().get(i);
         ISpecificationCase c2 = m2.getSpecificationCases().get(i);
         assertEquals("Got specifications cases of different type", c1.getType(), c2.getType());
         switch (c1.getType()) {
         case NodeTypes.BEHAVIOR_SPECIFICATION:
            equalsBehaviorSpecification((IBehaviorSpecification) c1, (IBehaviorSpecification) c2, ignoreOffsets);
            break;
         case NodeTypes.LIGHTWEIGHT_SPECIFICATION:
            equalsLightWeightSpecification((ILightweightSpecification) c1, (ILightweightSpecification) c2, ignoreOffsets);
            break;
         default:
            fail("Get unsupported type " + c1.getType());
         }
      }
      
   }

}
