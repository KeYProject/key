

package paycard;


public class LogRecord {

    private /*@ spec_public @*/ static int transactionCounter = 0;

    private /*@ spec_public @*/ int balance = -1;
    private /*@ spec_public @*/ int transactionId = -1;
    private /*@ spec_public @*/ boolean empty = true;
    
    /*@ public invariant
      @     !empty ==> (balance >= 0 && transactionId >= 0);
      @*/
    

    public /*@pure@*/ LogRecord() {}


    /*@ public normal_behavior
      @   requires balance >= 0 && transactionCounter >= 0;
      @   assignable empty, this.balance, transactionId, transactionCounter;
      @   ensures this.balance == balance 
      @           && transactionId == \old(transactionCounter);
      @   ensures \inv && transactionCounter >= 0;
      @*/
    public /*@helper@*/ void setRecord(int balance) throws CardException {
	if(balance < 0) {
	    throw new CardException();
	}
    	this.empty = false;
    	this.balance = balance;
        this.transactionId = transactionCounter++;
    }

    
    /*@ public normal_behavior
      @   ensures \result == balance;
      @*/
    public /*@pure helper@*/ int getBalance() {
	return balance;
    }

    
    /*@ public normal_behavior
      @   ensures \result == transactionId;
      @*/
    public /*@pure helper@*/ int getTransactionId() {
	return transactionId;
    }
}
