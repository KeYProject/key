package test;

public class ReferencingClass {
    
    private int balance;
    ReferencedClass otherProject = new ReferencedClass(); 
   
/*@ normal_behavior
  @ ensures \result = otherProject.aNewName;
  @ assignable \nothing;
  @*/
   private int returnOtherProjectsField() {
      return otherProject.aNewName;
   }
   
}