package org.key_project.extsourceview.transformer;

public enum InsertionType {

    ASSUME("assume"),             // @assume            clause
    ASSERT("assert"),             // @assert            clause
    ASSIGNABLE("assignable"),     // @assert_assignable clause
    ASSUME_ERROR("assume_error"), // transform-failure (but continueOnError == true)
    ASSERT_ERROR("assert_error"); // transform-failure (but continueOnError == true)

    private final String name;

    InsertionType(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }
}