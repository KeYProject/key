package de.uka.ilkd.key.java.abstraction;

/**
 * A program model element representing methods.
 */
public interface Method extends Member, ClassTypeContainer {

    /**
     * Checks if this member is abstract. A constructor will report <CODE>false</CODE>.
     *
     * @return <CODE>true</CODE> if this member is abstract, <CODE>false</CODE> otherwise.
     * @see recoder.abstraction.Constructor
     */
    boolean isAbstract();

    /**
     * Checks if this method is native. A constructor will report <CODE>false</CODE>.
     *
     * @return <CODE>true</CODE> if this method is native, <CODE>false</CODE> otherwise.
     * @see recoder.abstraction.Constructor
     */
    boolean isNative();

    /**
     * Checks if this method is synchronized. A constructor will report <CODE>false</CODE>.
     *
     * @return <CODE>true</CODE> if this method is synchronized, <CODE>false</CODE> otherwise.
     * @see recoder.abstraction.Constructor
     */
    boolean isSynchronized();

}
