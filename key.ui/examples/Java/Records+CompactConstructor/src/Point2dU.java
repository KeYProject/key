public record Point2dU(int x, int y) {
    Point2dU {
        if(x<0) x *= -1;
        if(y<0) y *= -1;
    }
}

class Use {
    /*@ normal_behavior ensures true; requires true; */
    public void m() {
        var p = new Point2dU(1, -2);
        //@assert p.x()>0 && p.y()>0;
    }
}
