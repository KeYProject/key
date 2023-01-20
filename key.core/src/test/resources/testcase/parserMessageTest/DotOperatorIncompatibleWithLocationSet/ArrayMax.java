//MSG .*[.].operator.*not compatible.*location set.*this[.][*].*
//LINE 11
//COL 28

class ArrayMax {

    int max;

    /*@ public normal_behaviour
      @   requires a.length > 0;
      @   assignable this.*.*;
      @*/
    public int m(int a[]) {
        max = a[0];

       for(int i = 0; i < a.length; i++) {
            if(max < a[i]) {
                max = a[i];
            }
        }
        return max;
    }

}

