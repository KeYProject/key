
// TODO: Add a .key file that runs auto; and then z3 on all remaining open goals.

class MinExcludant0 {

    /*@ requires (\forall int n; 0 <= n < s.length; (\exists int m; 0 <= m < s.length; (\bigint)s[m] == n));
      @ ensures (\forall int k; 0 <= k < s.length; (\bigint)s[k] < s.length);
      @ // measured_by s.length;
      @ static no_state lemma nospace(\seq s) \by {
      @   oss; macro "nosplit-prop";
      @   obtain \bigint N \from_goal;     
      @   cut s.length == 0 \by {
      @     case "true":
      @       auto; // the base case is simple and obvious
      @     case "false":
      @       obtain \bigint sm \such_that (\bigint)s[sm] == s.length - 1 && 0 <= sm < s.length \by {
      @          oss; macro "nosplit-prop";
      @          inst var:"n" with:s.length-1;
      @          auto;
      @       }
      @       obtain \seq t = s[0 .. sm] + s[sm+1 .. s.length];
      @       use_lemma nospace(t);
      @       assert (\forall int n; 0 <= n < t.length; (\exists int m; 0<=m<t.length; (\bigint)t[m] == n)) \by {
      @         obtain \bigint n1 \from_goal;
      @         obtain int m1 \such_that 0<=m1<s.length&& (\bigint)s[m1] == n1 \by smt solver: "Z3"; 
      @         assert (\bigint)t[m1] == n1  && m1 < sm || m1 == sm || m1 > sm && (\bigint)t[m1-1] == n1 \by auto;
      @         macro "nosplit-prop";
      @         inst var: "m" with: m1-1;
      @         auto;
      @       }
      @       cut N <= sm \by {
      @         case "true": // the easy case: up to the split point
      @           auto;
      @         case "false": // tricky bit if behind the element that was removed.
      @           oss;
      @           inst var: "k" with: N-1;
      @           auto;
      @       }      
      @   }
      @ };
      @*/

    /*@ normal_behaviour
      @  ensures (\forall int k; 0 <= k < a.length; a[k] != \result);
      @  ensures (\forall int u; 0 <= u < \result; (\exists int j; 0 <= j < a.length; a[j] == u));
      @  assignable \strictly_nothing;
      @*/
    static int mex0(int[] a) {
        int n = a.length;

        /*@ maintaining 0 <= v <= n;
          @ maintaining (\forall int u; 0 <= u < v; (\exists int j; 0 <= j < a.length; a[j] == u));
          @ decreases n - v;
          @ assignable \strictly_nothing;
          @*/
        for (int v = 0; v < n; v++) {
            int i = 0;
            /*@ maintaining 0 <= i <= n;
              @ maintaining (\forall int k; 0 <= k < i; a[k] != v);
              @ decreases n - i;
              @ assignable \strictly_nothing;
              @*/
            while (i < n && a[i] != v)
                i++;
            
            if (i == n)
                return v;

        }
        //@ use_lemma nospace(\array2seq(a));
        return n;
    }
}
