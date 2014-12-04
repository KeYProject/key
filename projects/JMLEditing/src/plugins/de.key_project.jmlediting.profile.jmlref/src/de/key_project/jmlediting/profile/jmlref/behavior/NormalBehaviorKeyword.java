package de.key_project.jmlediting.profile.jmlref.behavior;

public class NormalBehaviorKeyword extends AbstractBehaviorKeyword {

   public NormalBehaviorKeyword() {
      super("normal_behavior", "normal_behaviour");
   }

   @Override
   public String getDescription() {
      return "A normal_behavior specification case is just syntactic sugar for a behavior specification case with an implicit signals clause \"signals (java.lang.Exception) false;\" ruling out abrupt termination, i.e., the throwing of any exception.";
   }

}
