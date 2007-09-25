package src;

/**
* @throughout self.empty = false implies (self.balance >= 0 and self.date <> null and self.transactionId > 0)
* @invariants self.empty = false implies (self.balance >= 0 and self.date <> null and self.transactionId > 0)
*/
public class LogRecord {
    private int balance = -1;
    private SaleDate date = null;
    private int transactionId = -1;
    private boolean empty = true;

    public LogRecord() {}

    /**
     * @preconditions true
     * @postconditions true
     * @modifies  self.balance, self.date, self.transactionId
     */
    public boolean setRecord(int balance, src.SaleDate date, int transactionId) {
    	this.empty = false;
    	this.balance = balance;
        this.date = date;
        this.transactionId = transactionId;
//		this.empty = false;
        return true;
    }

    public int getBalance() {
		return balance;
    }

    public SaleDate getSaleDate() {
        return date;
    }

    public int getTransactionId() {
		return transactionId;
    }
}
