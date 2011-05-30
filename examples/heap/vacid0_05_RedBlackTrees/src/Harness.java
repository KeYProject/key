package vacid0.redblacktree;

/**
 * Harness suggested by Leino and Moska&#0322; for runtime-checking the implementation.
 * Not implementation-aware (makes only use of the map interface).
 * @author bruns
 *
 */
public class Harness {

  public static void redBlackTestHarness() {
    AbstractMap a = new RedBlackTree(0); 
    AbstractMap b = new RedBlackTree(1);
    a.replace(1, 1); b.replace(1, 10);
    a.replace(2, 2); b.replace(2, 20);
    assert(a.lookup(1) == 1 && a.lookup(42) == 0);
    assert(b.lookup(1) == 10 && b.lookup(42) == 1);
    a.remove(1); b.remove(2);
    assert(a.lookup(1) == 0 && a.lookup(42) == 0);
    assert(b.lookup(2) == 1 && b.lookup(42) == 1);
  }

  public static void main(String[] arrrgggh){
      redBlackTestHarness();
  }

}
