package cp;

public class C1 extends C {

  public static void m_C1() {
    that.is.going.to.be.discarded();
  }

  // cp.Unresolved2 must be a fully qualified reference!
  public cp.Unresolved2 q() {
    return null;
  }

}
