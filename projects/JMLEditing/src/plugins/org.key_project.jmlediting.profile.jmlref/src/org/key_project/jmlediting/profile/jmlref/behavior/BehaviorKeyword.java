package org.key_project.jmlediting.profile.jmlref.behavior;

public class BehaviorKeyword extends AbstractBehaviorKeyword {

   public BehaviorKeyword() {
      super("behavior", "behaviour");
   }

   @Override
   public String getDescription() {
      return "The behavior specification case is the most general form of specification case. All other forms of specification cases simply provide some syntactic sugar for special kinds of behavior specification cases.";
   }

}
