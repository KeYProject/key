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
