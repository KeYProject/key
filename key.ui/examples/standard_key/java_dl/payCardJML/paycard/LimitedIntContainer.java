

package paycard;


public interface LimitedIntContainer {
    
    /*@ public instance model int value;
      @ public instance model boolean regularState;
      @*/

    /*@ public normal_behavior
      @   ensures regularState ==> \result == value;
      @*/
    /*@ pure @*/ int available();
}
