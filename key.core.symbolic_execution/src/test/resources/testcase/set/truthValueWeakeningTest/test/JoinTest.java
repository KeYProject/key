public class JoinTest {
   /*@ normal_behavior
     @ ensures \result >= 0;
     @ assignable \strictly_nothing;
     @*/
    public static int zero(int value) {
        if (value < 0) {
            value = value * -1;
        }
        //@ merge_point;
        int result = value;
        return result;
    }
}