// An example of a secure password file.                                      //
//                                                                            //
// A straight forward implementation of a password file. This implementation  //
// can be proven to be secure. It froms the basis for the other implementation//
// variants.                                                                  //


class SumExample {

    //@ model \seq anyUser;

    private int[] values;


    public SumExample(int[] values) {
        this.values = values;
    }


    /*@ normal_behavior
      @     ensures     \result == (\bsum int i; 0; values.length; values[i]);
      @     accessible  values, values[*];
      @     modifies    \less_than_nothing;
      @     declassify  (\bsum int i; 0; values.length; values[i])
      @                 \to \seq(\result);
      @     respects    anyUser;
      @     respects    \result;
      @*/
    public int getSum() {
        int sum = 0;
        /*@ loop_invariant
          @     0 <= i
          @  && i <= values.length
          @  && sum == (\bsum int j; 0; i; values[j]);
          @ assignable \less_than_nothing;
          @ decreases values.length - i;
          @*/
        for (int i = 0; i < values.length; i++) {
            sum += values[i];
        }
        return sum;
    }
}