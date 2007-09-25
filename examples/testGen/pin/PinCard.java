public class PinCard{

    protected int pin;
    protected int counter_pin;
    protected boolean permission_session;

    /*@ public normal_behavior
      @  requires 0 <= counter_pin && counter_pin <= 3;
      @  assignable permission_session, counter_pin, pin;
      @  ensures counter_pin==0 ==> \result==9840;
      @  ensures (\old(pin) != oldPin || \old(counter_pin) == 0) ?
      @          (\old(pin) == pin && (\result==9840 || \result==9804)) : 
      @          (pin == newPin && \result==9000);
      @*/
    public int changePin(int oldPin, int newPin){
	int sw;
	if(counter_pin==0){
	    sw = 9840;
	}else{
	    if(pin==oldPin){
		pin = newPin;
		counter_pin = 3;
		permission_session = true;
		sw = 9000;
	    }else{
		if(counter_pin == 1){
		    counter_pin = 0;
		    permission_session = false;
		    sw = 9840;
		}else{
		    counter_pin--;
		    sw = 9804;
		}
	    }
	}
	return sw;
    }

    public void setPin(int pin){
	this.pin = pin;
    }

} 

