package testTermParserSorts;

class IntegerMethods {
/*@ pure */ public int queryByte(byte b) { return 0; }
/*@ pure */ public int queryChar(char c) { return 0; }
/*@ pure */ public int queryShort(short s) { return 0; }
/*@ pure */ public int queryInt(int i) { return 0; }
/*@ pure */ public int queryLong(long l) { return 0; }

/*@ pure */ public int queryByteArray(byte[] b) { return 0; }
/*@ pure */ public int queryCharArray(char[] c) { return 0; }
/*@ pure */ public int queryShortArray(short[] s) { return 0; }
/*@ pure */ public int queryIntArray(int[] i) { return 0; }
/*@ pure */ public int queryLongArray(long[] l) { return 0; }

/*@ pure */ public int queryMixed(byte b, char c[], short s, int i[], long l) { return 0; }
/*@ pure */ public static int queryMixedStatic(byte b, char c[], short s, int i[], long l) { return 0; }
}
