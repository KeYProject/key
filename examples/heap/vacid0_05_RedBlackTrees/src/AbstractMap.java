package vacid0.redblacktree;

/**
 * Map interface without data structure exposure.
 * @author bruns
 *
 */
interface AbstractMap{

    //@ model instance int defaultValue;
    //@ model instance int[] contents;

    //@ initially (\forall int i; 0 <= i; contents[i] == defaultValue);

    //@ requires key >= 0;
    //@ ensures contents[key] == value;
    public void replace (int key, int value);

    //@ requires key >= 0;
    //@ ensures contents[key] == defaultValue;
    public void remove (int key);

    //@ requires key >= 0;
    //@ ensures \result == contents[key];
    public /*@ pure @*/ int lookup (int key);
}
