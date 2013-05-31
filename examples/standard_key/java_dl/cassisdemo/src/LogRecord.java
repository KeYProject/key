// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

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
