class Test {
    /*@ normal_behavior
        ensures \result;
     */
    public boolean foo() {
        String a = "abc";
        String b = "abd";
        return a.compareTo(b) == 1;
    }

}