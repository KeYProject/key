public class KiAdClass extends AdClass {
    private int a = 1;
    private int d = 4;
    protected int e = 5;
}

class AdClass {
    private int a = 0;
    protected int b = 0;
    public int c = 0;

    private AdClass next;
    private AdClass left;
    private AdClass right;
}
