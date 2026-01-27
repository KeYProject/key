package org.key_project.extsourceview.transformer;

/**
 * Type of InsertionTerms (used to determine JML keyword and position)
 */
public enum InsertionType {

    ASSUME(1, "assume"), // @assume clause
    ASSERT(2, "assert"), // @assert clause
    ASSIGNABLE(9, "assignable"), // @assert_assignable clause
    ASSUME_ERROR(-2, "assume_error"), // transform-failure (but continueOnError == true)
    ASSERT_ERROR(-1, "assert_error"); // transform-failure (but continueOnError == true)

    public final int order;
    public final String name;

    InsertionType(int order, String name) {
        this.order = order;
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }
}
