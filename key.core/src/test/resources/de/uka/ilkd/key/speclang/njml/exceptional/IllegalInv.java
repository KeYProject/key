// exceptionClass: PosConvertException
// msgContains: mismatched input ';'
// position: 17/19
// verbose: true
// broken: false

// currently reports the wrong position

/* Used to be an NPE
Caused by: java.lang.NullPointerException: Cannot read field "second" because "pos" is null
	at de.uka.ilkd.key.java.Recoder2KeY.reportError(Recoder2KeY.java:1258)
	at de.uka.ilkd.key.java.Recoder2KeY.recoderCompilationUnitsAsFiles(Recoder2KeY.java:401)
	at de.uka.ilkd.key.java.Recoder2KeY.readCompilationUnitsAsFiles(Recoder2KeY.java:299)
*/

class IllegalInv {
    /*@ invariant ;*/
}
