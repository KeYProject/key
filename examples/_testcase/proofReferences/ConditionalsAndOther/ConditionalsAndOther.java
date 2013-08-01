
public class ConditionalsAndOther {
	private int x;
	
	private int y;

	private boolean b;
	
	private Exception e;
	
	private ExceptionWrapper ew;
	
	/*@
     @ ensures \result == (x == 0);
     @*/
	public boolean switchInt() {
	   switch (x) {
	      case 0 : return true;
  	      default : return false;
	   }
	}
	
	/*@
	  @ ensures \result == b;
	  @*/
	public boolean ifBoolean() {
		if (b) {
			return true;
		}
		else {
			return false;
		}
	}
	
	/*@
	  @ ensures \result == x < y;
	  @*/
	public boolean ifLess() {
		if (x < y) {
			return true;
		}
		else {
			return false;
		}
	}
	
	/*@
	  @ ensures \result == x <= y;
	  @*/
	public boolean ifLessEquals() {
		if (x <= y) {
			return true;
		}
		else {
			return false;
		}
	}
	
	/*@
	  @ ensures \result == x <= y;
	  @*/
	public boolean ifEquals() {
		if (x == y) {
			return true;
		}
		else {
			return false;
		}
	}
	
	/*@
	  @ ensures \result == x != y;
	  @*/
	public boolean ifNotEquals() {
		if (x != y) {
			return true;
		}
		else {
			return false;
		}
	}
	
	/*@
	  @ ensures \result == x >= y;
	  @*/
	public boolean ifGreaterEquals() {
		if (x >= y) {
			return true;
		}
		else {
			return false;
		}
	}
	
	/*@
	  @ ensures \result == x > y;
	  @*/
	public boolean ifGreater() {
		if (x > y) {
			return true;
		}
		else {
			return false;
		}
	}
   
   /*@
     @ ensures \result == b;
     @*/
   public boolean questionBoolean() {
      return b ? true : false;
   }
   
   /*@
     @ ensures \result == x < y;
     @*/
   public boolean questionLess() {
      return x < y ? true : false;
   }
   
   /*@
     @ ensures \result == x <= y;
     @*/
   public boolean questionLessEquals() {
      return x <= y ? true : false;
   }
   
   /*@
     @ ensures \result == x <= y;
     @*/
   public boolean questionEquals() {
      return x == y ? true : false;
   }
   
   /*@
     @ ensures \result == x != y;
     @*/
   public boolean questionNotEquals() {
      return x != y ? true : false;
   }
   
   /*@
     @ ensures \result == x >= y;
     @*/
   public boolean questionGreaterEquals() {
      return x >= y ? true : false;
   }
   
   /*@
     @ ensures \result == x > y;
     @*/
   public boolean questionGreater() {
      return x > y ? true : false;
   }
   
   /*@
     @ ensures true;
     @*/
   public boolean ifIncrementsAndDecrements() {
      if (x++ * y++ > --y * x--) {
         return true;
      }
      else {
         return false;
      }
   }
   
   /*@
     @ ensures true;
     @*/
   public boolean questionIncrementsAndDecrements() {
      return x++ * y++ > --y * x-- ? true : false;
   }
   
   /*@
     @ ensures \result == b;
     @*/
   public boolean returnBoolean() {
      return b;
   }

   /*@
     @ ensures \result == (x == y);
     @*/
   public boolean returnEquals() {
      return x == y;
   }

   /*@
     @ ensures \result == true;
     @*/
   public boolean returnComplex() {
      return x == y && b || !b && x != y;
   }
   
   /*@
     @ ensures true;
     @*/
   public void methodCall() {
      doNothing(x, b);
   }
   
   /*@
     @ ensures true;
     @*/
   public void methodCallAssignment() {
      doNothing(x++ + y + 1, b);
   }
   
   /*@
     @ ensures true;
     @*/
   public void methodCallCondtional() {
      doNothing(x, b || y == 0);
   }
   
   public void doNothing(int localInt, boolean localBoolean) {
   }
   
   /*@ exceptional_behavior
     @ requires e != null;
     @ signals (Exception e) \not_specified;
     @*/
   public void throwsException() throws Exception {
      throw e;
   }
   
   /*@ exceptional_behavior
     @ requires ew != null && ew.wrapped != null;
     @ signals (Exception e) \not_specified;
     @*/
   public void throwsNestedException() throws Exception {
      throw ew.wrapped;
   }
   
   public static class ExceptionWrapper {
      public Exception wrapped;
   }
   
   /*@ requires b == false;
     @ ensures true;
     @*/
   public void whileBoolean() {
      while (b) {
      }
   }
   
   /*@ requires x != y;
     @ ensures true;
     @*/
   public void whileEquals() {
      while (x == y) {
      }
   }
   
   /*@ requires b == false;
     @ ensures true;
     @*/
   public void doWhileBoolean() {
      do {
      }
      while (b);
   }
   
   /*@ requires x != y;
     @ ensures true;
     @*/
   public void doWhileEquals() {
      do {
      }
      while (x == y);
   }
   
   /*@ requires b == false;
     @ ensures true;
     @*/
   public void forBoolean() {
      for(int i = 0; b; i++) {
      }
   }
   
   /*@ requires x != y;
     @ ensures true;
     @*/
   public void forEquals() {
      for (int i = 0; x == y; i++) {
      }
   }
}
