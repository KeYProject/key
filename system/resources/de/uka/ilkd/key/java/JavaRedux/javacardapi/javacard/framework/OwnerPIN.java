package javacard.framework;

public class OwnerPIN implements PIN {

    private byte _maxPINSize;
    //@ public invariant _maxPINSize > 0;
    private byte _maxTries;
    //@ public invariant _maxTries > 0;

    private /*@ spec_public non_null @*/ byte[] _temps;
    /*@ public invariant _temps.length == 1 &&
                         JCSystem.isTransient(_temps) == JCSystem.CLEAR_ON_RESET;
      @*/

    private /*@ spec_public non_null @*/ boolean[] _isValidated;
    /*@ public invariant _isValidated.length == 1 &&
                         JCSystem.isTransient(_isValidated) == JCSystem.CLEAR_ON_RESET;
      @*/

    private /*@ spec_public non_null @*/ byte[] _pin;
    /*@ public invariant _pin.length == _maxPINSize + 1 &&
                         JCSystem.isTransient(_pin) == JCSystem.NOT_A_TRANSIENT_OBJECT;
      @*/

    //@ ensures \result == _isValidated[0];
    protected boolean /*@ pure @*/ getValidatedFlag() {
        return _isValidated[0];
    }

    /*@ public normal_behavior
          requires true;
          ensures getValidatedFlag() == value;
          assignable _isValidated[0];
    @*/
    protected void setValidatedFlag(boolean value) {
        _isValidated[0] = value;
    }

    /*@ public normal_behavior 
          requires maxTries > 0;
          requires maxPINSize > 0;
          ensures _maxPINSize == maxPINSize;
          ensures _maxTries == maxTries;
          ensures getTriesRemaining() == maxTries;
          ensures !isValidated();
          assignable _isValidated, _temps, _pin, _maxPINSize, _maxTries;
    @*/
    public OwnerPIN(byte maxTries, byte maxPINSize) throws PINException {
        if (maxPINSize < 1) {
            PINException.throwIt(PINException.ILLEGAL_VALUE);
        }
        _pin = new byte[maxPINSize + 1];
        // KeYHelper.setJavaOwner(_pin, this);
        _temps = JCSystem.makeTransientByteArray((short) 1,
                JCSystem.CLEAR_ON_RESET);
        // KeYHelper.setJavaOwner(_temps, this);
        _isValidated = JCSystem.makeTransientBooleanArray((short) 1,
                JCSystem.CLEAR_ON_RESET);
        // KeYHelper.setJavaOwner((java.lang.Object)_isValidated, this);
        _pin[0] = maxTries;
        _maxTries = maxTries;
        _maxPINSize = maxPINSize;
        _isValidated[0] = false;
    }

    /*@ public behavior
          requires JCSystem.npe != null;
          requires JCSystem.aioobe != null;
          requires PINException._systemInstance != null;
          requires PINException._systemInstance.<inv>;
          ensures getTriesRemaining() == _maxTries;
          ensures !isValidated();
          signals (NullPointerException npe) npe == JCSystem.npe && pin == null;
          signals (ArrayIndexOutOfBoundsException aioobe)
             aioobe == JCSystem.aioobe && (length < 0 || offset < 0 || offset + length > pin.length);
          signals (PINException pe)
             pe == PINException._systemInstance &&
             ((PINException)pe).getReason() == PINException.ILLEGAL_VALUE &&
             length > _maxPINSize;
          signals_only NullPointerException, ArrayIndexOutOfBoundsException, PINException;
          assignable _pin[*];
      @*/
    public void update(/*@ nullable @*/ byte[] pin, short offset, byte length)
            throws PINException, NullPointerException {
        if (length > _maxPINSize) {
            PINException.throwIt(PINException.ILLEGAL_VALUE);
        }
        Util.arrayCopy(pin, offset, _pin, (short) 1, length);
        _pin[0] = _maxTries;
        setValidatedFlag(false);
    }

    public void resetAndUnblock() {
        setValidatedFlag(false);
        _pin[0] = _maxTries;
    }

    public boolean isValidated() {
        return getValidatedFlag();
    }

    //@ ensures \result == _pin[0];
    public /*@pure@*/ byte getTriesRemaining() {
        return _pin[0];
    }

    public boolean check(/*@ nullable @*/ byte[] pin, short offset, byte length)
            throws NullPointerException, ArrayIndexOutOfBoundsException {
        setValidatedFlag(false);
        if (getTriesRemaining() == 0)
            return false;
        _temps[0] = (byte) (_pin[0] - 1);
        Util.arrayCopyNonAtomic(_temps, (short) 0, _pin, (short) 0, (short) 1);
        if (length != _maxPINSize)
            return false;
        if (Util.arrayCompare(_pin, (short) 1, pin, offset, length) == 0) {
            setValidatedFlag(true);
            _pin[0] = _maxTries;
            return true;
        }
        return false;
    }

    public void reset() {
        if (isValidated())
            resetAndUnblock();
    }
}
