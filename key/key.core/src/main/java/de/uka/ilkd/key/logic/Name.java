package de.uka.ilkd.key.logic;

/**
 * A Name object is created to represent the name of an object which usually implements the
 * interface {@link Named}.
 *
 * <p>
 * It wraps a string object. To save memory and to speed up equality checks, the wrapped strings are
 * stored in their {@linkplain String#intern() interned} representation.
 */
public class Name implements Comparable<Name> {

    private static final String NONAME = "_noname_";

    private final /** Interned */
    String nameString;

    /**
     * creates a name object
     */
    public Name(String n) {
        nameString = (n == null ? NONAME : n).intern();
    }

    @Override
    public String toString() {
        return nameString;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Name)) {
            return false;
        }
        // since ALL nameStrings are interned, equality can be safely reduced to
        // identity in THIS case:
        return nameString == ((Name) o).nameString;
    }

    @Override
    public int compareTo(Name o) {
        return nameString.compareTo(o.nameString);
    }

    @Override
    public int hashCode() {
        return nameString.hashCode();
    }

}
