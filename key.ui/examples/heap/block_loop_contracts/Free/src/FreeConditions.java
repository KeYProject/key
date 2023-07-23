public class FreeConditions {

    public static int field;
    public static /*@nullable@*/ Object obj;

    /*@ public normal_behavior
      @ ensures field == 42;
      @*/
    public static void blockContract0() {
        /*@ public normal_behavior
          @ requires_free field == 41;
          @ ensures field == 42;
          @*/
        {
            ++field;
        }
    }

    /*@ public normal_behavior
      @ ensures field == 42;
      @*/
    public static void blockContract1() {
        /*@ public normal_behavior
          @ ensures_free field == 42;
          @*/
        {
            ++field;
        }
    }
    
    /*@ public normal_behavior
      @ ensures field == 21; */
    public static void blockContract2() {
        /*@ public normal_behavior
          @ ensures field == 21; 
          @ assignable field;
          @ assignable_free obj; */
        { field = 21; 
          obj = new Object(); }
        
        /*@ public normal_behavior
          @ ensures true; 
          @ assignable \nothing;
          @ assignable_free field; */
        { field = 42;
          new Object(); }
        
        /*@ public normal_behavior
          @ ensures true; 
          @ assignable \strictly_nothing;
          @ assignable_free \nothing; */
        { new Object(); }
    }
    
    /*@ public normal_behavior
      @ ensures field == 21; */
    public static void blockContract3() {
        /*@ public normal_behavior
          @ ensures field == 21; 
          @ assignable \strictly_nothing;
          @ assignable_free field; */
        { field = 42;
          obj = new Object(); }
    }

    /*@ public normal_behavior
      @ ensures field == 42;
      @*/
    public static void assertions0() {
        //@ assume field == 41;
        ++field;
        //@ assert field == 42;

        ;
    }

    /*@ public normal_behavior
      @ ensures field == 42;
      @*/
    public static void assertions1() {
        //@ assume field == 42;

        ;
    }
}
