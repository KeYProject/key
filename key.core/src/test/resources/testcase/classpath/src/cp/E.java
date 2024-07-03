/* Enums are (partly) supported as well */

package cp;

enum E {
  e1(1), e2(20), e3(300);
  public static final E e4 = e2;
  E(int i) { }
}

