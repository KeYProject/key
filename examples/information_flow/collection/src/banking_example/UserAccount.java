/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package banking_example;


/**
 *
 * @author christoph
 */
public class UserAccount {
    private /*@ spec_public */ int userID;
    private /*@ spec_public */ char[] password;
    private BankAccount[] bankAccounts;

    /*@ public ghost \seq employeeViewOnUserAccount;
      @ public invariant employeeViewOnUserAccount ==
      @     \seq( this, userID, bankAccounts,
      @           (\seq_def int i; 0; bankAccounts.length; bankAccounts[i].customerViewOnBankAccount) );
      @
      @ public ghost \seq bankCustomerView;
      @ public invariant bankCustomerView ==
      @     \seq( this, userID, bankAccounts, password,
      @           (\seq_def int i; 0; password.length; password[i]),
      @           (\seq_def int i; 0; bankAccounts.length; bankAccounts[i].customerViewOnBankAccount) );
      @*/

    /*@ normal_behavior
      @ ensures \result == (    userID == this.userID
      @                      && password.length == this.password.length
      @                      && (\forall int i; 0 <= i && i < password.length;
      @                             password[i] == this.password[i]) );
      @ ensures \result == tryLogin(userID, password);
      @ determines  employeeViewOnUserAccount \by \itself;
      @ determines  bankCustomerView \by  \itself;
      @ assignable \strictly_nothing;
      @*/
    public boolean tryLogin(int userID, char[] password) {
        boolean equals = (    this.userID == userID
                           && this.password.length == password.length );
        /*@ loop_invariant 0 <= i && i <= password.length;
          @ loop_invariant equals == (    userID == this.userID
          @                      && password.length == this.password.length
          @                      && (\forall int j; 0 <= j && j < i;
          @                             password[j] == this.password[j]) );
          @ assignable \strictly_nothing;
          @ decreases password.length - i;
          @*/
        for(int i = 0; equals && i < password.length; i++) {
            equals = (this.password[i] == password[i]);
        }
        return equals;
    }

    /*@ normal_behavior
      @ determines  employeeViewOnUserAccount \by \itself;
      @ determines  bankCustomerView \by  \itself;
      @ assignable \strictly_nothing;
      @*/
    public /*@ nullable */ BankAccount getBankAccount(int number) {
        if (number < 0 || bankAccounts.length <= number) {
            return null;
        }
        return bankAccounts[number];
    }
}
