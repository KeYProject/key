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
 * @invariants self.log <> null and self.log.length = self.logFileSize and self.logFileSize = 20 and self.currentRecord >= 0 and self.currentRecord < self.logFileSize and (self.currentRecord + 1).mod(self.logFileSize) >= 0 and (self.currentRecord + 1).mod(self.logFileSize) < self.logFileSize
 */
public class LogFile {
    private final static int logFileSize = 20;
    private int currentRecord;
    private LogRecord[] log = new LogRecord[logFileSize];

    public LogFile() {
		for(int i=0;i<log.length; i++)
            log[i] = new LogRecord();
        currentRecord = -1;
    }

    public void addRecord(int balance, SaleDate date, int transactionId){
	currentRecord++;
	if(currentRecord == logFileSize) currentRecord = 0;
        int posToInsert = currentRecord;
	if(log[posToInsert] == null)
            log[posToInsert] = new LogRecord();
        log[posToInsert].setRecord(balance, date, transactionId);
    }

}
