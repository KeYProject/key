
package cp;

public class C1 extends C {

  public static int field; // should not be removed
    
  /*@ public normal_behaviour
    @   ensures true;
    @*/
  public static void m_C1() {
//    that.is.going.to.be.discarded();
  }

}
