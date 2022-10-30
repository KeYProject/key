package org.key_project.extsourceview.transformer;

public enum InsertionType {

    REQUIRES_EXPLICT("requires_explicit"),   // @requires clause
    REQUIRES_IMPLICT("requires_implicit"),   // autom. generated requires term

    ENSURES_EXPLICT("ensures_explicit"),     // @ensures clause
    ENSURES_IMPLICT("ensures_implicit"),     // autom. generated requires term
    ENSURES_UNKNOWN("ensures_unknown");      // no origin

    private final String name;

    InsertionType(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }
}