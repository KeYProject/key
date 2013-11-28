/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package banking_example;


/**
 *
 * @author christoph
 */
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
