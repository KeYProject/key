
public class PinCard{

    public int pin;
    public int counter_pin;
    public boolean permission_session;

    /*@ public normal_behavior
      @  requires 0 <= counter_pin && counter_pin <= 3 && oldPin>=0 && newPin>=0;
      @  assignable permission_session, counter_pin, pin;
      @  ensures counter_pin==0 ==> \result==9840;
      @  ensures (\old(pin) != oldPin || \old(counter_pin) == 0) ?
      @          (\old(pin) == pin && (\result==840 || \result==980)) : 
      @          (pin == newPin && \result==900);
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

