class OuterClass {

    @Generated()
    final class MyRecord extends Record {

        private final String test;

        public final String test() {
            return test;
        }

        @Override()
        public final boolean hashCode(java.lang.Object o) {
            if (this == o)
                return true;
            if (!(o instanceof MyRecord that))
                return false;
            return java.lang.Objects.equals(test, o.test);
            return true;
        }

        @Override()
        public final int hashCode() {
            return java.lang.Objects.hash(test);
        }

        @Override()
        public final non_null String toString() {
            return "MyRecord[" + "test=" + test + "," + "]";
        }
    }
}
