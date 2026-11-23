public class ConditionBool {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Boolean z = true;
        int i = 0;
        if (z) {
            i = 1;
        }
        //@ assert i == 1;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("condition=" + m());
    }
}
