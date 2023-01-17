package transformations;

import java.util.*;

import static java.lang.System.out;
import static java.lang.Thread.*;
import java.io.*;

import com.sun.org.apache.bcel.internal.generic.LXOR;

abstract class Generic<T extends List & Helper> {
	T foo(T p) { 
		Helper h = foo(p);
		foo(p).bar();
		return null; 
	}
}

interface Helper {
	void bar();
}

class SList<T> implements List<T> {
	T get(int i) { return null; }
}

class Whatever {
	SList<Integer> somelist;
	List<Integer> anotherList;
	void foo() {
		somelist.get(0).byteValue();
		anotherList.get(0).byteValue();
	}
}

abstract class AnotherHelper implements List, Helper {
}

abstract class Extender extends Generic<AnotherHelper> { 
}

abstract class Extender2 extends Generic { 
}

abstract class Extender3<E extends List & Helper> extends Generic<E> {
	E foo2() { 
		return foo(null); 
	}
	Helper foo3() { 
		return foo(null); 
	}
}

interface RecoderList<E> extends Iterable<E> {
	void trimToSize();
	E get(int i);
	int size();
    
//    static final RecoderList EMPTY_LIST = new RecoderArrayList(0);
}

interface RecoderMutableList<E> extends RecoderList<E>, List<E> {
	RecoderMutableList<E> deepClone();
    void ensureCapacity(int minCapacity);
}

interface RecoderProgramElementList<E extends List> extends RecoderMutableList<E> {
	RecoderProgramElementList<E> deepClone();
}

public class Dummy {
	void unenhanceMe() {
		String s[] = new String[10];
		for (String x: s) {
			x.toLowerCase();
		}
		
		for (String x: s) 
			x.toLowerCase();
		
		l1: l2: l3: for (String x: s) {
			break l1;
		}
		
		List<? extends List> extl;
		for (List q: extl) {
			q.clear();
		}
		
		List<String> l = new ArrayList<String>(10);
		for (String x : l) {
			x.toLowerCase();
		}
		
		l1: for (String x: l) {
			break l1;
		}
		int i = 0;
		Object a = null;
		
		RecoderMutableList<ArrayList> rml = null;
		rml.iterator().next().ensureCapacity(15);
		for (ArrayList x : rml) {
			x.ensureCapacity(5);
		}
	}
	
	// some helper methods for iDontLikeBoxing
	int intMeth() { 
		return 0; 
	}
	Integer integerMeth() { 
		return null; 
	}
	void pm1(Object x, int i, Object y) { }
	void pm2(Integer io, int i) { }
	
	void iDontLikeBoxing() {
		int a = new Integer(5);
		Integer b = 5;
		Boolean c = new Boolean(true);
		assert (c);
		assert c;
		pm1(null, b, null);
		pm2(3, 5);
		pm2(b, b);
		pm2(b, 3);
		pm2(3, b);
		(true ? "hello, world" : 5).getClass();
	}
	@ItsAnAnnotation @ItsAnAnnotation.ItsAnInnerAnnotation interface EmptyIF { }
	interface BadStyling extends ItsAnAnnotation { }
	interface BadStyling2 extends ItsAnotherAnnotation.Inner { }
	
	void staticImportsSuck() {
		out.print("Hello, world");
		int i = MAX_PRIORITY;
	}
	
	void noMoreVarArgs(String ... x) {
		noMoreVarArgs("Hello, World");
		noMoreVarArgs("Hello", "World");
		noMoreVarArgs();
	}
	
	void noMoreVarArgs2(int i, String ... x) {
		noMoreVarArgs2(1, "Hello, World");
		noMoreVarArgs2(2, "Hello", "World");
		noMoreVarArgs2(3);
        noMoreVarArgs2(1, new java.lang.String[] { "Hello, World" });
        noMoreVarArgs2(2, new java.lang.String[] { "Hello", "World" });
        noMoreVarArgs2(3, new java.lang.String[] { });
	}
	
	static void bar(Enum1 a) {
		switch (a) {
		  case A:
		  case B:
		  case C:
		}
	}
}

@interface ItsAnAnnotation {
	int x() default 5;
	@interface ItsAnInnerAnnotation {
		int y() default 0;
	}
}

@interface ItsAnotherAnnotation {
	@interface Inner {
		
	}
}

@interface JustAnotherAnnotation {

}

class XY {
	public XY clone() throws CloneNotSupportedException { return (XY)super.clone(); }
	{
		try {
		XY x = clone();
		} catch (CloneNotSupportedException cnse) {}
	}
}

enum Enum1 {
	A,
	B { },
	C(3) { },
	D(5),
	E { void foo() { } }
	;
	Enum1(int x) {
	}
	Enum1() {
	}
	void foo() { }
}

