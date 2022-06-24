class Test {
    /*@
      requires ary.length > 0;
      requires pos >= 0;
      ensures \result ==
                  (\sum int i; pos <= i < ary.length; ary[i]);
      measured_by ary.length - pos;
      assignable \strictly_nothing;
     */
    public int sum(int[] ary, int pos) {
        if( pos < 0 || pos >= ary.length)
            return 0;
        return ary[pos] + sum(ary,pos+1);
    }
}
