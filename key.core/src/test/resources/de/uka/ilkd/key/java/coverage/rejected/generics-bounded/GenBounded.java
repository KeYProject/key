public class GenBounded {
    interface S { }
    static class Box<T extends S> { T v; }
    static class Impl implements S { }
    Box<Impl> b = new Box<Impl>();
}
