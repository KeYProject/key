package testTermParserHeap;

class A {

private int f;
A next;
int[] array;

static int staticField;
static int[] staticArray;
static int staticMethod() {
	return 0;
}

/*@ pure */ public int query(int a) { return 0; }
/*@ pure */ public A getNext() { return next; }
/*@ pure */ public int queryOverridden() { return 0; }
/*@ pure */ private int queryRedefined() { return 0; }

}

class A1 extends A {
private  int f; 
/*@ ensures \result == queryOverridden(); */
/*@ pure */ public int queryOverridden() { return 1; }
/*@ ensures \result == queryRedefined(); */
/*@ pure */ private int queryRedefined() { return 1; }

}
