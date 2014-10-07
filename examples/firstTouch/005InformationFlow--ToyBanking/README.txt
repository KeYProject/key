Information flow example.

The example is a toy implementation of a banking system. It is ensured that customers may observe only data of their own user- and bank-accounts. Employees my observe everything but the passwords of the customers. Further, customers may see their user account only after a successful log in.


--- source code ---

public class Bank {

    private UserAccount[] userAccounts;

    /*@ public ghost \seq bankEmployeeView;
      @ public invariant bankEmployeeView ==
      @     \seq( userAccounts,
      @           (\seq_def int i; 0; userAccounts.length; userAccounts[i].employeeViewOnUserAccount) );
      @
      @ public invariant ( \forall int i; 0 <= i && i < userAccounts.length; \invariant_for(userAccounts[i]) );
      @
      @ public ghost int anyID;
      @ public invariant 0 <= anyID && anyID < userAccounts.length;
      @*/

    /*@ normal_behavior
      @ determines  \result
      @        \by  userID,
      @             (\seq_def int i; 0; password.length; password[i]),
      @             ( (   0 <= userID && userID < userAccounts.length
      @                && userAccounts[userID].tryLogin(userID, password))
      @                    ? userAccounts[userID] : null )
      @        \declassifies userAccounts[userID].tryLogin(userID, password);
      @ determines  bankEmployeeView \by \itself;
      @ // The underspecified integer anyID is used to quantify over all userAccounts:
      @ determines  userAccounts[anyID].bankCustomerView \by \itself;
      @*/
    public /*@ nullable */ UserAccount login(int userID,
                                             char[] password) {
        UserAccount result = null;
        if (0 <= userID && userID < userAccounts.length) {
            boolean loginSuccessful = userAccounts[userID].tryLogin(userID, password);
            if (loginSuccessful) {
                result = userAccounts[userID];
            }
        }
        return result;
    }

}


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


public class BankAccount {
    private int balance;
    private int id;

    /*@ public ghost \seq customerViewOnBankAccount;
      @ public invariant customerViewOnBankAccount == \seq(this, balance, id);
      @*/

    /*@ normal_behavior
      @ determines customerViewOnBankAccount \by  \itself;
      @ assignable \strictly_nothing;
      @*/
    int getId() {
        return id;
    }

    /*@ normal_behavior
      @ determines customerViewOnBankAccount \by  \itself;
      @ assignable \strictly_nothing;
      @*/
    int getBalance() {
        return balance;
    }

    /*@ normal_behavior
      @ determines customerViewOnBankAccount \by  \itself
      @            \declassifies amount;
      @ assignable balance, customerViewOnBankAccount;
      @*/
    void depositMoney(int amount) {
        this.balance = this.balance - amount;
        //@ set customerViewOnBankAccount = \seq_concat(\seq_singleton(this), \seq_concat(\seq_singleton(balance), \seq_singleton(id)));
        ;
    }
}
