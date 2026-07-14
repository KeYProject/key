public class Classes {
    interface Shape { int area(); }
    static class Square implements Shape {
        int s;
        public int area() { return s * s; }
    }
    int use() { Square q = new Square(); q.s = 3; return q.area(); }
}
