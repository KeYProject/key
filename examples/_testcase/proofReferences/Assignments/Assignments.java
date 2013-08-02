
public class Assignments {
	int value;
	
	int anotherValue;
	
	int[] array;
	
	MyClass myClass;
	
	Assignments next;
	
	/*@
	  @ ensures value == \old(value) + 1;
	  @*/
	public void incrementEnd() {
		value++;
	}
	
	/*@
	  @ ensures value == \old(value) + 1;
	  @*/
	public void incrementBegin() {
		++value;
	}
	
	/*@
	  @ ensures value == \old(value) - 1;
	  @*/
	public void decrementEnd() {
		value--;
	}
	
	/*@
	  @ ensures value == \old(value) - 1;
	  @*/
	public void decrementBegin() {
		--value;
	}
   
   /*@ requires array != null && array.length == 1;
     @ ensures array[0] == \old(array[0]) + 1;
     @*/
   public void incrementArrayEnd() {
      array[0]++;
   }
   
   /*@ requires array != null && array.length == 1;
     @ ensures array[0] == \old(array[0]) + 1;
     @*/
   public void incrementArrayBegin() {
      ++array[0];
   }
   
   /*@ requires array != null && array.length == 1 && anotherValue == 0;
     @ ensures array[anotherValue] == \old(array[anotherValue]) - 1;
     @*/
   public void decrementArrayEnd() {
      array[anotherValue]--;
   }
   
   /*@ requires array != null && array.length == 1 && anotherValue == 0;
     @ ensures array[anotherValue] == \old(array[anotherValue]) - 1;
     @*/
   public void decrementArrayBegin() {
      --array[anotherValue];
   }
	
	/*@
	  @ ensures value == \old(value) + anotherValue;
	  @*/
	public void add() {
		value += anotherValue;
	}
	
	/*@ 
	  @ ensures value == \old(value) - anotherValue;
	  @*/
	public void sub() {
		value -= anotherValue;
	}
	
	/*@
	  @ ensures value == \old(value) * anotherValue;
	  @*/
	public void mul() {
		value *= anotherValue;
	}
	
	/*@ requires anotherValue != 0;
	  @ ensures value == \old(value) / anotherValue;
	  @*/
	public void div() {
		value /= anotherValue;
	}

	/*@ requires anotherValue != 0;
	  @ ensures value == \old(value) % anotherValue;
	  @*/
	public void mod() {
		value %= anotherValue;
	}
	
	/*@
	  @ ensures value == anotherValue;
	  @*/
	public void assign() {
		value = anotherValue;
	}
	
	/*@ requires myClass != null && myClass.child != null;
	  @ ensures myClass.child.childValue == myClass.child.anotherChildValue;
	  @*/
	public void nestedValue() {
		myClass.child.childValue = myClass.child.anotherChildValue;
	}
   
   /*@ requires myClass != null && myClass.child != null;
     @ ensures myClass.child.childValue == myClass.child.anotherChildValue + myClass.child.thirdChildValue;
     @*/
   public void nestedValueAdd() {
      myClass.child.childValue = myClass.child.anotherChildValue + myClass.child.thirdChildValue;
   }
	
	/*@ requires myClass != null && myClass.child != null && myClass.child.childArray != null;
	  @ requires myClass.child.childArray.length == 2;
	  @ ensures myClass.child.childArray[0] == myClass.child.childArray[1];
	  @*/
	public void nestedArray() {
		myClass.child.childArray[0] = myClass.child.childArray[1];
	}
	
	public static class MyClass {
		public MyChildClass child;
	}
	
	public static class MyChildClass {
		public int childValue;

		public int anotherChildValue;

      public int thirdChildValue;

		public int[] childArray;
	}
	
   /*@ 
     @ ensures next == this;
     @*/
   public void assignmentWithSelf() {
      this.next = this;
   }
}
