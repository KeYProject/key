
public class LoopContractExamplesEnhancedFor {

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @ assignable arr[*];
      @*/
    public static int sum_loopContract_onNormalLoop(int[] arr) {
        int sum = 0;
        
        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= idx && idx <= arr.length;
          @ requires sum == (\sum int i; 0 <= i && i < idx; arr[i]);
          @ ensures  sum == (\sum int i; 0 <= i && i < arr.length; arr[i]);
          @ assignable \nothing;
          @ decreases arr.length - idx;
          @*/
        for (int idx = 0; idx < arr.length; ++idx) {
            sum += arr[idx];
        }
        
        return sum;
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @ assignable arr[*];
      @*/
    public static int sum_loopContract_onLoop(int[] arr) {
        int sum = 0;
        
        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= \index && \index <= arr.length;
          @ requires sum == (\sum int i; 0 <= i && i < \index; arr[i]);
          @ ensures  sum == (\sum int i; 0 <= i && i < arr.length; arr[i]);
          @ assignable \nothing;
          @ decreases arr.length - \index;
          @*/
        for (int el : arr) {
            sum += el;
        }
        
        return sum;
    }
    
    /*@ normal_behavior
      @ requires arr != null;
      @ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @ assignable arr[*];
      @*/
    public static int sum_loopContract_onBlock(int[] arr) {
        int sum = 0;
        
        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= \index && \index <= arr.length;
          @ requires sum == (\sum int i; 0 <= i && i < \index; arr[i]);
          @ ensures  sum == (\sum int i; 0 <= i && i < arr.length; arr[i]);
          @ assignable \nothing;
          @ decreases arr.length - \index;
          @*/
        {
            for (int el : arr) {
                sum += el;
            }
        }
        
        return sum;
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @ assignable arr[*];
      @*/
  public static int sum_loopInvariant(int[] arr) {
      int sum = 0;
      
      /*@ loop_invariant arr != null && 0 <= \index && \index <= arr.length;
        @ loop_invariant sum == (\sum int i; 0 <= i && i <  \index; arr[i]);
        @ assignable \nothing;
        @ decreases arr.length - \index;
        @*/
      for (int el : arr) {
          sum += el;
      }
      
      return sum;
  }
}
