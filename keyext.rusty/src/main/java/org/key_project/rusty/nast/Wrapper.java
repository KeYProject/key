package org.key_project.rusty.nast;

public class Wrapper {
    public interface Crate {

    }

    private static native Crate start();

    static {
        System.loadLibrary("rust_wrapper");
    }

    public static Crate parse() {
        return Wrapper.start();
    }
}
