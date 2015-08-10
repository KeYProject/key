package test;

public class ReferencingClass {
    
    private int balance;
    ReferencedClass otherProject = new ReferencedClass(); 
   
/*@ normal_behavior
  @ ensures \result = otherProject.balance;
  @ assignable \nothing;
  @*/
   private int returnOtherProjectsField() {
      return otherProject.balance;
   }
   
}