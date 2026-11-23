public class PostfixCall {
    static int id(int x) {
        return x;
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = 42;
        int i = id(a++);
        int j = a;
        //@ assert i == 42;
        //@ assert j == 43;
        return i + j;
    }

    public static void main(String[] args) {
        System.out.println("call=" + m());
    }
}
