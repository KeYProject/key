package paycard;

public interface LimitedIntContainer{
    /*@
      @ public model int value;
      @ public model boolean regularState;
      @*/

    /*@ public normal_behavior
      @   ensures regularState ==> \result == value;
      @*/
    int /*@ pure @*/ available(); 

}
