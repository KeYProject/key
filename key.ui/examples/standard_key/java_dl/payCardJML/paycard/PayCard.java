

package paycard;


public class PayCard implements LimitedIntContainer {
    
    /*@ spec_public @*/ int limit = 1000;
    /*@ spec_public @*/ int unsuccessfulOperations;
    /*@ spec_public @*/ int id;
    /*@ spec_public @*/ int balance = 0;
    /*@ spec_public @*/ protected LogFile log;   
    

    /*@ public invariant log.\inv;
      @ public invariant balance == log.logArray[log.currentRecord].balance;
      @ public invariant balance >= 0;
      @ public invariant limit > 0;
      @ public invariant available() >= 0;
      @ public invariant unsuccessfulOperations >= 0;
      @*/
    
    /*@ public represents value = balance;
      @ public represents regularState = (unsuccessfulOperations <= 3);
      @*/

    
    /*@ public normal_behavior
      @   requires limit > 0;
      @   requires LogRecord.transactionCounter >= 0;
      @   assignable LogRecord.transactionCounter;
      @   ensures LogRecord.transactionCounter >= 0;
      @*/
    public PayCard(int limit) {
        balance = 0;
        unsuccessfulOperations = 0;
        this.limit = limit;
	this.log = new LogFile();
	log.addRecord(balance);
    }

    
    /*@ public normal_behavior
      @   requires LogRecord.transactionCounter >= 0;
      @   assignable LogRecord.transactionCounter;
      @   ensures LogRecord.transactionCounter >= 0;
      @*/
    public PayCard() {
	balance = 0;
        unsuccessfulOperations = 0;
	this.log = new LogFile();
	log.addRecord(balance);
    }
    

    /*@ public behavior
      @   requires LogRecord.transactionCounter >= 0;
      @   requires amount > 0;
      @   assignable balance, unsuccessfulOperations, log.currentRecord, 
      @              (\infinite_union int x; 0 <= x && x < log.logArray.length ? log.logArray[x].* : \empty),
      @              LogRecord.transactionCounter;
      @   ensures balance >= \old(balance);
      @*/
   public void charge(int amount) {
        if(this.balance + amount >= this.limit || amount <= 0) {
            this.unsuccessfulOperations++;
        } else {
            this.balance = this.balance + amount;
	    try {
		log.addRecord(balance);
	    } catch(CardException e) {
		throw new IllegalStateException();
	    }
        }
    }

   
    /*@ also public normal_behavior
      @   ensures \result == balance || unsuccessfulOperations > 3;
      @*/
    public /*@pure@*/ int available() {
	if(unsuccessfulOperations <= 3) {
	    return this.balance;
        }
        return 0;
    }
    

    public String infoCardMsg() {
	return " Current balance on card is " + balance;
    }
}
