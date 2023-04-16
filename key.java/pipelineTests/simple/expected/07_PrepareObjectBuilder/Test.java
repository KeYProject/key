public class Test {

    public static int abc;

    static {
        // should be resolved to 2
        abc = 1 + 1;
    }

    public int memberVar;

    {
        memberVar = 42;
    }

    @javax.annotation.processing.Generated()
    static private boolean $classInitializationInProgress;

    @javax.annotation.processing.Generated()
    static private boolean $classErroneous;

    @javax.annotation.processing.Generated()
    static private boolean $classInitialized;

    @javax.annotation.processing.Generated()
    static private boolean $classPrepared;

    static private void $clprepare() {
    }

    static public void $clinit() {
        if (!@($classInitialized)) {
            if (!@($classInitializationInProgress)) {
                if (!@(this.$classPrepared)) {
                    @($clprepare());
                }
                if (@($classErroneous)) {
                    throw new java.lang.NoClassDefFoundError();
                }
                @($classInitializationInProgress) = true;
                try {
                    @(java.lang.Object.$clinit());
                } catch (java.lang.Error err) {
                    @($classInitializationInProgress) = false;
                    @($classErroneous) = true;
                    throw err;
                } catch (java.lang.Throwable twa) {
                    @($classInitializationInProgress) = false;
                    @($classErroneous) = true;
                    throw new java.lang.ExceptionInInitializerError(twa);
                }
                @($classInitializationInProgress) = false;
                @($classErroneous) = false;
                @($classInitialized) = true;
            }
        }
    }

    protected void $prepare() {
    }

    private void $prepareEnter() {
    }
}

public class SubClass extends Test {

    public int memberVar;

    {
        memberVar = 41;
    }

    @javax.annotation.processing.Generated()
    static private boolean $classInitializationInProgress;

    @javax.annotation.processing.Generated()
    static private boolean $classErroneous;

    @javax.annotation.processing.Generated()
    static private boolean $classInitialized;

    @javax.annotation.processing.Generated()
    static private boolean $classPrepared;

    static private void $clprepare() {
    }

    static public void $clinit() {
        if (!@($classInitialized)) {
            if (!@($classInitializationInProgress)) {
                if (!@(this.$classPrepared)) {
                    @($clprepare());
                }
                if (@($classErroneous)) {
                    throw new java.lang.NoClassDefFoundError();
                }
                @($classInitializationInProgress) = true;
                try {
                    @(Test.$clinit());
                } catch (java.lang.Error err) {
                    @($classInitializationInProgress) = false;
                    @($classErroneous) = true;
                    throw err;
                } catch (java.lang.Throwable twa) {
                    @($classInitializationInProgress) = false;
                    @($classErroneous) = true;
                    throw new java.lang.ExceptionInInitializerError(twa);
                }
                @($classInitializationInProgress) = false;
                @($classErroneous) = false;
                @($classInitialized) = true;
            }
        }
    }

    protected void $prepare() {
    }

    private void $prepareEnter() {
    }
}
