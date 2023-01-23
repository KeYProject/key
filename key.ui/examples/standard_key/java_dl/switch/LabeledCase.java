class LabeledCase {
    /*@ public normal_behaviour
        ensures \result <==> n == -1;
     @*/
    public boolean m(int n) {
        _l0: {
            switch(n) {
                case 0:
                    break;
                case -1:
                    break _l0;
                default:
            }
            return false;
        }
        return true;
    }
}
