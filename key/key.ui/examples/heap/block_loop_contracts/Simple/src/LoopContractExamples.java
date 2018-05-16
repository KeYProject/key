public class LoopContractExamples {

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures (\forall int i; 0 <= i && i < arr.length;
      @     arr[i] == \old(arr[i]) + 1);
      @ assignable arr[*];
      @*/
    public static void mapIncrement_loopContract(int[] arr) {
        int i = 0;
        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= i && i <= arr.length;
          @ ensures (\forall int j; \before(i) <= j && j < arr.length;
          @         arr[j] == \before(arr[j]) + 1);
          @ assignable arr[i .. arr.length];
          @ decreases arr.length - i;
          @*/
        {
            while (i < arr.length) {
                ++arr[i];
                ++i;
            }
        }
    }
    
    /*@ normal_behavior
      @ requires arr != null;
      @ ensures (\forall int i; 0 <= i && i < arr.length;
      @     arr[i] == \old(arr[i]) + 1);
      @ assignable arr[*];
      @*/
    public static void mapIncrement_loopContract_forLoop(int[] arr) {
        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= i && i <= arr.length;
          @ ensures (\forall int j; \before(i) <= j && j < arr.length;
          @         arr[j] == \before(arr[j]) + 1);
          @ assignable arr[i .. arr.length];
          @ decreases arr.length - i;
          @*/
        {
            for (int i = 0; i < arr.length; ++i) {
                ++arr[i];
            }
        }
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures (\forall int i; 0 <= i && i < arr.length;
      @     arr[i] == \old(arr[i]) + 1);
      @*/
    public static void mapIncrement_loopInvariant(int[] arr) {
        int i = 0; 

        /*@ loop_invariant (0 <= i && i <= arr.length)
          @     && (\forall int j; 0 <= j && j < i; arr[j] == \old(arr[j]) + 1)
          @     && (\forall int j; i <= j && j < arr.length;
          @         arr[j] == \old(arr[j]));
          @ assignable arr[i .. arr.length];
          @ decreases arr.length - i;
          @*/
        while (i < arr.length) {
            ++arr[i];
            ++i;
        }
    }
}