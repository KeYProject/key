package bank;

/**
 * Singleton class for empty lists of transactions
 * @stereotype singleton
 */
public /*@ pure @*/ class TransactionListNIL extends TransactionList {
    
    /**
     * This class is a singleton, to access the only object use
     * <code>TransactionList.EMPTY_LIST</code>
     */
    protected TransactionListNIL() {}
    
    /**
     * @return the first element of <code>this</code> list, or
     *         <code>null</code> iff this list is empty
     * 
     * @stereotype query
     */
    public Transaction head () {
        return null;
    }

    /**
     * @return the tail (the list without its first element) of
     *         <code>this</code> list, or <code>null</code> iff this list is
     *         empty
     * 
     * @stereotype query
     */
    public TransactionList tail () {
        return null;
    }

    /**
     * @return <code>true</code> iff <code>this</code> list is empty
     * 
     * @stereotype query
     */
    public boolean isEmpty () {
        return true;
    }

    /**
     * @return the length of this list
     * 
     * @stereotype query
     */
    public int length () {
        return 0;
    }
}
