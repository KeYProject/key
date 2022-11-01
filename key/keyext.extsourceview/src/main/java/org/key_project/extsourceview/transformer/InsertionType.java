package org.key_project.extsourceview.transformer;

public enum InsertionType {

    REQUIRES("requires"),   // @requires clause
    ENSURES("ensures"),     // @ensures clause
    ASSIGNABLE("assignable");     // @ensures clause

    private final String name;

    InsertionType(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }
}