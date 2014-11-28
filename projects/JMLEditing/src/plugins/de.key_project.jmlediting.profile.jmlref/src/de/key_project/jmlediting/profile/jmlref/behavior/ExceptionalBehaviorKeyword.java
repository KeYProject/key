package de.key_project.jmlediting.profile.jmlref.behavior;

public class ExceptionalBehaviorKeyword extends AbstractBehaviorKeyword {

   public ExceptionalBehaviorKeyword() {
      super("exceptional_behavior", "exceptional_behaviour");
   }

   @Override
   public String getDescription() {
      return "An exceptional behavior specification case specifies a precondition which guarantees that the method throws an exception, if it terminates, i.e., a precondition which prohibits the method from terminating normally.";
   }

}
