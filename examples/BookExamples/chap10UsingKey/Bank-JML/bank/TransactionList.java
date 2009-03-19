package bank;

/**
 * Simple implementation of a list datatype for transactions. All
 * <code>TransactionList</code> subclasses are immutable, i.e. the objects
 * cannot be altered after creation. There are two subclasses, which correspond
 * to the two common constructors NIL (singleton) and CONS of lists.
 */
public /*@ pure @*/ abstract class TransactionList {

    //@ static public invariant EMPTY_LIST != null;
    public final static TransactionList EMPTY_LIST = new TransactionListNIL ();

    /**
     * @return the first element of <code>this</code> list, or
     *         <code>null</code> iff this list is empty
     */
    public abstract Transaction head ();

    /**
     * @return the tail (the list without its first element) of
     *         <code>this</code> list, or <code>null</code> iff this list is
     *         empty
     */
    public abstract TransactionList tail ();

    /**
     * @return <code>true</code> iff <code>this</code> list is empty
     */
    public abstract boolean isEmpty ();
    
    /**
     * @return the length of this list
     */
    public abstract int length ();

    /**
     * Construct a list whose first element is <code>trans</code>, and whose
     * tail is <code>this</code> list
     * 
     * @param trans
     *            the first element of the new list
     * @return the constructed list
     */
    public TransactionList prepend(Transaction trans) {
        return new TransactionListCons (trans, this);
    }
}
