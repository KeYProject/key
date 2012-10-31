package javacard.framework;

public interface PIN {

    public boolean isValidated();

    public byte getTriesRemaining();

    public boolean check(byte[] pin, short offset, byte length)
            throws NullPointerException, ArrayIndexOutOfBoundsException;

    public void reset();
}
