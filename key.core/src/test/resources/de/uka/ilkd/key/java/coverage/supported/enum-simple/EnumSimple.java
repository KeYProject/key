public class EnumSimple {
    enum Dir { UP, DOWN }
    Dir d = Dir.UP;
    boolean up() { return d == Dir.UP; }
}
