package de.key_project.jmlediting.profile.jmlref.behavior;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public abstract class AbstractBehaviorKeyword extends AbstractKeyword{

   private final DefaultBehaviorParser parser;
  
   public AbstractBehaviorKeyword(String... keywords) {
      super(keywords);
      this.parser = new DefaultBehaviorParser();
   }

   @Override
   public IKeywordParser createParser() {
      return this.parser;
   }

}
