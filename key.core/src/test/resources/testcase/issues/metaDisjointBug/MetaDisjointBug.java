// Contract must not be provable as i and j might have same value
// m(new Node[]{c}, 0, 0, b, 1)
public class MetaDisjointBug {
    /*@ public normal_behavior
      @ requires 0 <= i && i < a.length && 0 <= j && j < a.length;
      @ requires \typeof(a) == \type(Node[]);
      @ requires !\reach(a[i], a, b, n);
      @ ensures !\reach(a[i], a, b, n);
      @ assignable a[j];
      @*/
    public static void m(Node[] a, int i, int j, Node b, int n) {
        a[j] = b;
    }
}

final class Node {
}

