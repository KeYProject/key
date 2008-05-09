package bank;

/**
 * Abstract class for representing transactions. Each transaction is related to
 * exactly one account (this is not visible in this class, because transactions
 * are stored by accounts and not the other way round) and takes place at a
 * particular point of time. All <code>Transaction</code> subclasses are
 * immutable, i.e. the objects cannot be altered after creation
 */
public abstract class Transaction {
    
    /**
     * The date at which <code>this</code> transaction takes place
     */
    private final int date;
    
    public /*@ pure @*/ Transaction (final int date) {
        this.date = date;
    }
    
    /**
     * @return Returns the date at which <code>this</code> transaction takes
     *         place
     */
    public /*@ pure @*/ int getDate () {
        return date;
    }
    
    /**
     * The design pattern "Strategy" is used for implementing the
     * synchronisation of offline account proxies with the permanent accounts.
     * Invoking this method carries out <code>this</code> transaction an the
     * real account
     * 
     * @param target
     *            the permanent account on which <code>this</code> transaction
     *            is supposed to be carried out
     */
    public abstract void replay (PermanentAccount target);
}
