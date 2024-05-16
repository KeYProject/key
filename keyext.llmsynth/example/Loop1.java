class Loop1 {

    /*@ public invariant x>=0; @*/
    private /*@ spec_public @*/ int x;

    /*@ public normal_behavior
      @ requires x>=0;
      @ assignable \nothing;  // this is a ** constructor **, so the object does not yet exist, 
      @                       // hence "this" object's fields do not need to be in the assignable
      @ ensures this.x == x;
      @*/
    public Loop1(int x) {
        this.x = x;
    }

    /*@ public normal_behavior
      @ requires x > 0;
      @ ensures \result == 0;
      @*/
    public int method1() {
        int y = x;

        while (y > 0) {
            y--;
        }
        return y;
    }
}
