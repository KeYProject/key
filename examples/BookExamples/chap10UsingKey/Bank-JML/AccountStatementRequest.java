package bank;

/**
 * Class for representing the transaction of requesting a printed account
 * statement.
 * Objects of this class are immutable
 */
public class AccountStatementRequest extends Transaction {

    public /*@ pure @*/ AccountStatementRequest (int date) {
        super ( date );
    }

    /**
     * The design pattern "Strategy" is used for implementing the
     * synchronisation of offline account proxies with the permanent accounts.
     * Invoking this method carries out <code>this</code> transaction an the
     * real account. Note that the statement is requested for the correct date,
     * though this is meaningless because of the implementation of
     * <code>PermanentAccount.requestStatement</code>
     * 
     * @param target
     *            the permanent account on which <code>this</code> transaction
     *            is supposed to be carried out
     */
    public void replay (PermanentAccount target) {
        target.requestStatement ( getDate () );
    }

    public /*@ pure @*/ String toString () {
        return "" + getDate() + ":AccountStatement";
    }
}
