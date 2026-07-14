package sub;

import main.*;

public final class BOtherPackage {

  public static int callM() {
     A a = new A();
     byte val = 1;
     return a.m(val);
  }
}
