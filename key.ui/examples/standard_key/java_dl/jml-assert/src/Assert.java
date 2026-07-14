class Assert {

    /*@ normal_behavior
      @ ensures \result.length == x*x;
      @*/
    int[] createArray (int x) {
        final int z = x*x;
        //@ assert (\forall int j; 0 <= j < x; j * j >= 0);
        //@ assert z >= 0;
        { int y; } // workaround bug #1261
        return new int[z];
    }
}
