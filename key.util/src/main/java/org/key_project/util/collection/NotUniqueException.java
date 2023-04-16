package org.key_project.util.collection;



/** thrown if a duplicate is being added via addUnique() */
public class NotUniqueException extends Exception {

    private static final long serialVersionUID = 6565515240836947955L;
    final Object offender;

    public NotUniqueException(Object o) {
        offender = o;
    }

    @Override
    public String toString() {
        return "Tried to add a duplicate object to set. Offender is \n" + offender + "\nof class "
            + offender.getClass();
    }
}
