public class MostSimpleInner {

    public static class MyInnerClass {

        @javax.annotation.processing.Generated()
        static private boolean $classInitializationInProgress;

        @javax.annotation.processing.Generated()
        static private boolean $classErroneous;

        @javax.annotation.processing.Generated()
        static private boolean $classInitialized;

        @javax.annotation.processing.Generated()
        static private boolean $classPrepared;

        @javax.annotation.processing.Generated()
        static public model boolean <$staticInv>;

        @javax.annotation.processing.Generated()
        static public model boolean <$staticInv_free>;

        public static MyInnerClass $allocate();

        public MyInnerClass() {
        }

        public void $init() {
            super.$init();
            super.$init();
        }

        static private void $clprepare() {
        }

        static public void $clinit() {
            if (!@($classInitialized)) {
                if (!@($classInitializationInProgress)) {
                    if (!@($classPrepared)) {
                        //Created by ClassInitializeMethodBuilder.java:219
                        @($clprepare());
                    }
                    if (@($classErroneous)) {
                        throw new java.lang.NoClassDefFoundError();
                    }
                    //Created by ClassInitializeMethodBuilder.java:243
                    @($classInitializationInProgress) = true;
                    try {
                        @(java.lang.Object.$clinit());
                    }//Created by ClassInitializeMethodBuilder.java:194
                     catch (java.lang.Error err) {
                        //Created by ClassInitializeMethodBuilder.java:154
                        @($classInitializationInProgress) = false;
                        //Created by ClassInitializeMethodBuilder.java:155
                        @($classErroneous) = true;
                        throw err;
                    } catch (java.lang.Throwable twa) {
                        //Created by ClassInitializeMethodBuilder.java:154
                        @($classInitializationInProgress) = false;
                        //Created by ClassInitializeMethodBuilder.java:155
                        @($classErroneous) = true;
                        throw new java.lang.ExceptionInInitializerError(twa);
                    }
                    //Created by ClassInitializeMethodBuilder.java:249
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:251
                    @($classErroneous) = false;
                    //Created by ClassInitializeMethodBuilder.java:253
                    @($classInitialized) = true;
                }
            }
        }

        protected void $prepare() {
            super.$prepare();
        }

        private void $prepareEnter() {
            super.$prepare();
        }

        public MyInnerClass $create() {
            //Created by CreateBuilder.java:57
            this.$initialized = false;
            $prepareEnter();
            return this;
        }
    }

    @javax.annotation.processing.Generated()
    static private boolean $classInitializationInProgress;

    @javax.annotation.processing.Generated()
    static private boolean $classErroneous;

    @javax.annotation.processing.Generated()
    static private boolean $classInitialized;

    @javax.annotation.processing.Generated()
    static private boolean $classPrepared;

    @javax.annotation.processing.Generated()
    static public model boolean <$staticInv>;

    @javax.annotation.processing.Generated()
    static public model boolean <$staticInv_free>;

    public static MostSimpleInner $allocate();

    public MostSimpleInner() {
    }

    public void $init() {
        super.$init();
        super.$init();
    }

    static private void $clprepare() {
    }

    static public void $clinit() {
        if (!@($classInitialized)) {
            if (!@($classInitializationInProgress)) {
                if (!@($classPrepared)) {
                    //Created by ClassInitializeMethodBuilder.java:219
                    @($clprepare());
                }
                if (@($classErroneous)) {
                    throw new java.lang.NoClassDefFoundError();
                }
                //Created by ClassInitializeMethodBuilder.java:243
                @($classInitializationInProgress) = true;
                try {
                    @(java.lang.Object.$clinit());
                }//Created by ClassInitializeMethodBuilder.java:194
                 catch (java.lang.Error err) {
                    //Created by ClassInitializeMethodBuilder.java:154
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classErroneous) = true;
                    throw err;
                } catch (java.lang.Throwable twa) {
                    //Created by ClassInitializeMethodBuilder.java:154
                    @($classInitializationInProgress) = false;
                    //Created by ClassInitializeMethodBuilder.java:155
                    @($classErroneous) = true;
                    throw new java.lang.ExceptionInInitializerError(twa);
                }
                //Created by ClassInitializeMethodBuilder.java:249
                @($classInitializationInProgress) = false;
                //Created by ClassInitializeMethodBuilder.java:251
                @($classErroneous) = false;
                //Created by ClassInitializeMethodBuilder.java:253
                @($classInitialized) = true;
            }
        }
    }

    protected void $prepare() {
        super.$prepare();
    }

    private void $prepareEnter() {
        super.$prepare();
    }

    public MostSimpleInner $create() {
        //Created by CreateBuilder.java:57
        this.$initialized = false;
        $prepareEnter();
        return this;
    }
}
