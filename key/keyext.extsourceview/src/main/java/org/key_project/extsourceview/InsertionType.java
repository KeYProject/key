package org.key_project.extsourceview;

public enum InsertionType {

    REQUIRES_EXPLICT("requires_explicit"), // @requires clause
    ENSURES_EXPLICT("ensures_explicit"),   // @ensures clause

    REQUIRES_IMPLICT("requires_implicit"),   // autom. generated requires term
    ENSURES_IMPLICT("ensures_implicit");     // autom. generated requires term

    private final String name;

    private InsertionType(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }
}