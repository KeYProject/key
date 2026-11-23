public class IncrementSum {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = 42;
        int i = a++ + a++;
        int j = a;
        //@ assert i == 85;
        //@ assert j == 44;
        return i + j;
    }

    public static void main(String[] args) {
        System.out.println("sum=" + m());
    }
}
