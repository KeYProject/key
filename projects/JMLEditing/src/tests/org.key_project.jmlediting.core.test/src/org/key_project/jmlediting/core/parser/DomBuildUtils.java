package org.key_project.jmlediting.core.parser;

import static org.junit.Assert.fail;

import java.util.Arrays;

import org.key_project.jmlediting.core.dom.IBehaviorSpecification;
import org.key_project.jmlediting.core.dom.ILightweightSpecification;
import org.key_project.jmlediting.core.dom.IMethodSpecification;
import org.key_project.jmlediting.core.dom.ISpecificationCase;
import org.key_project.jmlediting.core.dom.ISpecificationStatement;
import org.key_project.jmlediting.core.dom.Visibility;
import org.key_project.jmlediting.core.parser.internal.BehaviorSpecification;
import org.key_project.jmlediting.core.parser.internal.LightweightSpecification;
import org.key_project.jmlediting.core.parser.internal.MethodSpecification;
import org.key_project.jmlediting.core.parser.internal.SpecificationStatement;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public class DomBuildUtils {

   static ISpecificationStatement buildStatementSpec(String keyword, String content) {
      return buildStatementSpec(keyword, 0, 0, content);
   }
   
   static ISpecificationStatement buildStatementSpec(String keyword,
         int start, int end, String content) {
      ISpecificationStatementKeyword sKeyword = null;
      for (ISpecificationStatementKeyword k : ProfileWrapper.testProfile
            .getSupportedSpecificationStatementKeywords()) {
         if (k.getKeyword().equals(keyword)) {
            sKeyword = k;
            break;
         }
      }
      if (sKeyword == null) {
         fail("Unable to find keyword");
      }
      return new SpecificationStatement(start, end, sKeyword, content);
   }
   
   static IBehaviorSpecification buildBehaviorSpec(Visibility vis,
         String keyword, ISpecificationStatement... statements) {
      return buildBehaviorSpec(vis, keyword, 0, 0, statements);
   }

   static IBehaviorSpecification buildBehaviorSpec(Visibility vis,
         String keyword, int start, int end,
         ISpecificationStatement... statements) {
      IJMLBehaviorKeyword bKeyword = null;
      for (IJMLBehaviorKeyword k : ProfileWrapper.testProfile.getSupportedBehaviors()) {
         if (k.getKeywords().contains(keyword)) {
            bKeyword = k;
            break;
         }
      }
      if (bKeyword == null) {
         fail("Unable to find keyword");
      }
      return new BehaviorSpecification(start, end, vis, bKeyword,
            Arrays.asList(statements));
   }
   
   static ILightweightSpecification buildLightweightSpec(ISpecificationStatement... stmts) {
      return buildLightweightSpec(0, 0, stmts);
   }
   
   static ILightweightSpecification buildLightweightSpec(int start, int end, ISpecificationStatement... stmts) {
      return new LightweightSpecification(start, end, Arrays.asList(stmts));
   }
   
   static IMethodSpecification buildMethodSpec(boolean isExtending, ISpecificationCase... cases) {
      return buildMethodSpec(0,0, isExtending, cases);
   }
   
   static IMethodSpecification buildMethodSpec(int start, int end, boolean isExtending, ISpecificationCase... cases) {
      return new MethodSpecification(start, end, isExtending, Arrays.asList(cases));
   }

}
