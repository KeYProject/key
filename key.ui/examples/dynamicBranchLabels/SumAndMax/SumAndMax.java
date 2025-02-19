class SumAndMax {

    int sum;
    int max;

    /*@ normal_behaviour
      @   requires R1: (\forall int i; 0 <= i && i < a.length; 0 <= a[i]);
      @   assignable sum, max;
      @   ensures E1: (\forall int i; 0 <= i && i < a.length; a[i] <= max);
      @   ensures E2: (a.length > 0
      @           ==> (\exists int i; 0 <= i && i < a.length; max == a[i]));
      @   ensures E3: sum == (\sum int i; 0 <= i && i < a.length; a[i]);
      @   ensures E4: sum <= a.length * max;
      @*/
    void sumAndMax(int[] a) {
        sum = 0;
        max = 0;
        int k = 0;

        /* @ loop_invariant I1: 0 <= k && k <= a.length;
          @ loop_invariant I2: (\forall int i; 0 <= i && i < k; a[i] <= max);
          @ loop_invariant I3: (k == 0 ==> max == 0);
          @ loop_invariant I4: (k > 0 ==> (\exists int i; 0 <= i && i < k; max == a[i]));
          @ loop_invariant I5: sum == (\sum int i; 0 <= i && i< k; a[i]);
          @ loop_invariant I6: sum <= k * max;
          @
          @  assignable sum, max;
          @  decreases a.length - k;
          @*/
        /*@ loop_invariant \lbl(I1, 0 <= k && k <= a.length)
          @             && \lbl(I2, (\forall int i; 0 <= i && i < k; a[i] <= max))
          @             && \lbl(I3, (k == 0 ==> max == 0))
          @             && \lbl(I4, k > 0 ==> (\exists int i; 0 <= i && i < k; max == a[i]))
          @             && \lbl(I5, sum == (\sum int i; 0 <= i && i< k; a[i]))
          @             && \lbl(I6, sum <= k * max);
          @
          @  assignable ASSIGN_LOOP: sum, max;
          @  decreases a.length - k;
          @*/
        while (k < a.length) {
            if (max < a[k]) {
                max = a[k];
            }
            sum += a[k];
            k++;
        }
    }
}
