package org.key_project.util.collection;


import org.jspecify.annotations.Nullable;

/** thrown if a duplicate is being added via addUnique() */
public class NotUniqueException extends Exception {
    private final @Nullable Object offender;

    public NotUniqueException(@Nullable Object o) {
        offender = o;
    }

    @Override
    public String toString() {
        return "Tried to add a duplicate object to set. Offender is \n" + offender +
            (offender != null ? " of class " + offender.getClass() : "");
    }
}
