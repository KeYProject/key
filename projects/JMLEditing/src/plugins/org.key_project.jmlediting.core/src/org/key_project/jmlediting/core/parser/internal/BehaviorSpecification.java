package org.key_project.jmlediting.core.parser.internal;

import java.util.Collections;
import java.util.List;

import org.key_project.jmlediting.core.dom.IBehaviorSpecification;
import org.key_project.jmlediting.core.dom.ISpecificationStatement;
import org.key_project.jmlediting.core.dom.Visibility;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;


public class BehaviorSpecification extends ASTNode implements IBehaviorSpecification{

   private IJMLBehaviorKeyword behaviorKeyword;
   
   private List<ISpecificationStatement> keywordStatements;
   
   private Visibility visibility;

   public BehaviorSpecification(int startOffset, int endOffset, Visibility visibility,
         IJMLBehaviorKeyword behaviorKeyword,
         List<ISpecificationStatement> keywordStatements) {
      super(startOffset, endOffset);
      this.visibility = visibility;
      this.behaviorKeyword = behaviorKeyword;
      this.keywordStatements = keywordStatements;
   }
   
   public BehaviorSpecification(int startOffset, int endOffset,
         IJMLBehaviorKeyword behaviorKeyword,
         List<ISpecificationStatement> keywordStatements) {
      this(startOffset, endOffset, Visibility.DEFAULT, behaviorKeyword, keywordStatements);
   }
   
   @Override
   public IJMLBehaviorKeyword getKeyword() {
      return behaviorKeyword;
   }
   
   @Override
   public List<ISpecificationStatement> getSpecificationStatements() {
      return Collections.unmodifiableList(keywordStatements);
   }

   @Override
   public Visibility getVisibility() {
      return this.visibility;
   }

}
