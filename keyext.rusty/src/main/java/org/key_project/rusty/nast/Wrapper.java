package org.key_project.rusty.nast;

public class Wrapper {
    public interface Crate {

    }

    private static native Crate start();

    static {
        System.loadLibrary("rustwrapper");
    }

    public static Crate parse() {
        return Wrapper.start();
    }
}
