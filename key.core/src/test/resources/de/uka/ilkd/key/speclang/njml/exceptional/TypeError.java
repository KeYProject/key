// exceptionClass: ConvertException
// msgContains: XXXX
// positiion: 19/xxx
// verbose: true
// broken: true

// This is broken since it exposes an IllegalArgumentException

/* Used to be an NPE 
Caused by: java.lang.NullPointerException: Cannot read field "second" because "pos" is null
	at de.uka.ilkd.key.java.Recoder2KeY.reportError(Recoder2KeY.java:1258)
	at de.uka.ilkd.key.java.Recoder2KeY.recoderCompilationUnitsAsFiles(Recoder2KeY.java:401)
	at de.uka.ilkd.key.java.Recoder2KeY.readCompilationUnitsAsFiles(Recoder2KeY.java:299)
*/

class TypeError {

    /*@ public normal_behaviour
      @  ensures 1 + 1 == true;
      @*/
    public void m() {}
}
