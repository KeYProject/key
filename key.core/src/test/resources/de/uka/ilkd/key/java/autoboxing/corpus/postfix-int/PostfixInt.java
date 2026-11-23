public class PostfixInt {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = 42;
        int i = a++;
        int j = a;
        //@ assert i == 42;
        //@ assert j == 43;
        return i + j;
    }

    public static void main(String[] args) {
        System.out.println("postfix=" + m());
    }
}
