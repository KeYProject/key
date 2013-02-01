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

import javacard.framework.JCSystem;

/**
* @throughout self.logFile.log.get(self.logFile.currentRecord).balance =
* self.balance
* @invariants self.logFile <> null
*/
public class Client {

    LogFile logFile;// = new LogFile();
    int balance = 1000;
    SaleDate currentDate;

    public Client() {
    }

    /**
     * @preconditions self.logFile <> null and self.currentDate <> null and
     * self.logFile.log <> null and self.logFile.logFileSize = 20 and
     * self.logFile.log.length = self.logFile.logFileSize and
     * self.logFile.currentRecord >=0 and self.logFile.currentRecord < self.logFile.logFileSize
     * @postconditions true
     */
    public void processSale(int amount, int sellerId) {
	JCSystem.beginTransaction();
	balance -= amount;
	if(balance < 0)
	     JCSystem.abortTransaction();
    else {
         logFile.addRecord(balance, currentDate, sellerId);
	    JCSystem.commitTransaction();
        }
    }
}
