public class VarArgs {
    int sum(int... xs) { int s = 0; for (int x : xs) s += x; return s; }
    int f() { return sum(1, 2, 3); }
}
