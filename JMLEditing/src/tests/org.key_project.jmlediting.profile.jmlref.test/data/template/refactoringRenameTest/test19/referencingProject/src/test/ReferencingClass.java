package test;

public class ReferencingClass {

    ReferencedClass otherProject = new ReferencedClass(); 
   
/*@ normal_behavior
  @ ensures \result = otherProject.balance;
  @ assignable \nothing;
  @*/
   private int returnOtherProjectsField() {
      return otherProject.balance;
   }
   
}