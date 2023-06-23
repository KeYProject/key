package org.key_project.util.model;

@SuppressWarnings("unused")
public class ClassB extends ClassA {
    private final int privateField = 42;

    protected int protectedField = 43;

    public int publicField = 44;

    int defaultField = 45;

    private final String onlyInB = "B";

    private int getPrivate() {
        return 662;
    }

    public int getPublic() {
        return 663;
    }

    protected int getProtected() {
        return 664;
    }

    int getDefault() {
        return 665;
    }

    private String onlyInB() {
        return "B";
    }
}
