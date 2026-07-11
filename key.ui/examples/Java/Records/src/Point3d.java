public record Point3d(int x, int y, int z) {
    /*@ normal_behavior ensures true; requires true; */
    public static void test() {
        Point3d p = new Point3d(1, 2, 3);

        //boolean b= p.equals(p);
        // @assert b;

        //@ assert p.x() == 1;
        //@ assert p.y() == 2;
        //@ assert p.z() == 3;

        //@assert p.equals(p);

        Point3d q = new Point3d(p.x, p.y, p.z);
        //@assert p.equals(q);
        //@assert q.equals(p);
    }
}

class Use {
    /*@ normal_behavior ensures true; requires true; */
    public static void m() {
        Point3d p = new Point3d(1, 2, 3);

        //boolean b= p.equals(p);
        // @assert b;

        //@ assert p.x() == 1;
        //@ assert p.y() == 2;
        //@ assert p.z() == 3;

        //@assert p.equals(p);

        Point3d q = new Point3d(p.x, p.y, p.z);
        //@assert p.equals(q);
        //@assert q.equals(p);
    }
}
