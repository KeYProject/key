class Test {
    //@ ghost int x;

    int a;

    //@ requires true; ensures x==a;
    void foo() {
        //@set x = 0;
        a = 0;
        //@set x = x + 1;
        a = a + 1;
        //@set x = x + 1;
        a = a + 1;
        //@set x = x + 1;
        a = a + 1;
        //@set x = x + 1;
        a = a + 1;
        //@set x = x + 1;
        a = a + 1;
    }


    //@ ghost int rec;
    int cer;

    //@ requires a >= 0; ensures rec == cer; measured_by a;
    int voo(int a) {
        if (a == 0) {
            //@ set rec = 0;
            cer = 0;
            return 0;
        } else {
            int r = voo(a - 1) + 1;
            //@ set rec = r;
            cer = r;
            return r;
        }
    }

}
