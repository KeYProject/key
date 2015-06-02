package org.key_project.jmlediting.ui.test.refactoring;

public class RefactoringTestClass {
    private int /*@ spec_public @*/ balance;
    private int /*@ spec_public @*/ overdraftLimit;
    
    /*@ normal_behavior
      @ requires balance + amount > overdraftLimit;
      @ ensures balance == \old(balance) + amount;
      @ assignable balance;
      @*/
    public void update(int amount) throws Exception {
        balance += amount;
    }
}
