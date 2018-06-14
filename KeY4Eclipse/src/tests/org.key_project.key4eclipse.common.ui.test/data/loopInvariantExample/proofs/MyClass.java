public class MyClass {

  public int a;
  public int b;
  public Object o;
  public /*@ nullable @*/ int[] array;

  /*@ public normal_behavior
        requires array != null;
        requires<permissions> \dl_readPermission(\permission(this.array));
        requires<permissions> (\forall int i; i>=0 && i<array.length;
            \dl_writePermission(\permission(this.array[i])));
        ensures (\forall int i; i>=0 && i<array.length; this.array[i] == 0);
        assignable<heap> array[*];
        assignable<permissions> \strictly_nothing;
    @*/
  public void method3() {
    /*@ loop_invariant i>=0 && i<=array.length;
        loop_invariant (\forall int j; j>=0 && j<array.length;
              j < i ? this.array[j] == 0 : this.array[j] == \old(this.array[j]));
        assignable<heap> array[*];
        assignable<permissions> \strictly_nothing;
        decreases array.length - i; @*/
    for(int i=0; i<array.length; i++) {
      array[i] = 0;
    }
  }
}
