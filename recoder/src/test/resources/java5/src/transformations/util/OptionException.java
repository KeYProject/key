// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

/**
 * @author RN
 */
public abstract class OptionException extends Exception {

    protected String opt;

    protected OptionException(String opt) {
        this.opt = opt;
    }

    public abstract String toString();

}