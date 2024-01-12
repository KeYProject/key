// reported by Dominic Steinhöfel
// issues #1 https://git.key-project.org/key/key/-/issues/1

class Steinhoefel1 {

    /*@ public normal_behavior
       @ ensures true;
       @*/
    public static int fib(int n) {
        int k0 = 1;
        int k1 = 1;

        //@ ghost int k0_old = k0;
        //@ ghost int k1_old = k1;

        /*@ loop_invariant
          @   n >= 2 ==> (
          @     i <= n + 1 &&
          @     k1 == k1_old + k0_old
          @   );
          @ decreases n-i+1;
          @ assignable \nothing;
          @*/
        for (int i = 2; i <= n; i++) {
            int tmp = k1;
            k1 = k0 + k1;
            k0 = tmp;

            //@ set k0_old = k0;
            //@ set k1_old = k1;
        }
        return k1;
    }
}