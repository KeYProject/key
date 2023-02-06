package testdata;

/**
 * Test data for RenameMethod and similar.
 * 
 * @author AM
 */

class MethodTestData {
    public int hashCode() {
        return super.hashCode();
    }

    public boolean equals(Object obj) {
        return super.equals(obj);
    }

    protected Object clone() {
        return new MethodTestData();
    }
}

interface IFirst {
    void baseAndChildAndIFirstMethod();

    void childAndIFirstMethod();

    void baseAndIFirstMethod();

    void baseAndIFirstISecondMethod();
}

interface ISecond {
    void baseAndIFirstISecondMethod();
}

abstract class Base {
    public void baseAndChildMethod() {
    }

    abstract public void baseAndChildAndIFirstMethod();

    public void baseAndIFirstMethod() {
    }

    public void baseAndIFirstISecondMethod() {
    }
}

class Child extends Base implements IFirst {
    public void childMethod() {
    }

    public void baseAndChildMethod() {
    }

    public void baseAndChildAndIFirstMethod() {
    }

    public void childAndIFirstMethod() {
    }

    protected Object clone() {
        return new Child();
    }
}

class GrandChild extends Child implements ISecond {
}