package transformations;

import java.io.Serializable;
import java.util.*;

class GenTest<T extends List> {
	T item;

	void setT(T t) {
		item = t;
	}

	T getT() {
		int i = item.size();
		return item;
	}

	Iterator<T> getIterator() {
		return null;
	}

	static GenTest<ArrayList> returnArrayList() {
		return new GenTest<ArrayList>();
	}
}

public class GenericTest {
	public static void main(String... args) {
		// test generic types declared in bytecode (i.e. test bytecode parser)
		List<String> l = new ArrayList<String>();
		l.add("Test");
		l.get(0).toLowerCase(); // return type of get() needs to be read from bytecode
		// a little more complicated (parameterized return value)
		l.iterator().next().toLowerCase();
		// test generic types declared in sourcecode
		GenTest<ArrayList> gt = new GenTest<ArrayList>();
		gt.setT(new ArrayList());
		System.out.println(gt.getT().size());
		GenTest.returnArrayList().getT().trimToSize();
		// now if return value is argumented itself
		gt.getIterator().next().trimToSize();
	}
}

// more complicated now

class A<T, U> {
	T getT() {
		return null;
	}

	U getU() {
		return null;
	}

	void setTV(T x) {
		// ignore...
	}

	void xyz(U u) {
		// ignore
	}
}

class B<T, U> {
	void foo() {
		A<GenTest<ArrayList>, GenTest<Vector>> a = new A<GenTest<ArrayList>, GenTest<Vector>>();
		a.getT().getT().trimToSize(); // ArrayList only
		a.getU().getT().addElement(null); // Vector only
	}
}

abstract class C<V, W> extends A<V, W> {
	private Map typeMap;

	V v;

	W w;

	void bar() {
		setTV(v);
		xyz(w);
	}

	C<V, W>[] c; // type arguments must be attached first, then the array needs to be created

	void bar2() {
		System.out.println(c.length);

		HashMap hm = new HashMap(); // raw type
		hm.put("Test", new int[5]); // test if paramMatches in DefaultProgramModelInfo allows this
	}
}

// now test generic methods...

class D {
    <T> T genMethTest(T arg) { /* return type is type of arg */
		return null;
	}

	<T> T genMethTest(T arg1, T arg2) {
		return null;
	}

	<T extends Runnable> void genExtTest(T arg) {
		arg.run();
	}

	void bar() {
		this.<String> genMethTest("Test").toLowerCase(); // explicit generic invocation
		this.genMethTest("Test").toLowerCase(); // type inference
		this.<String> genMethTest("Test", "Test").toLowerCase(); // explicit generic invocation
		this.genMethTest("Test", "Test").toLowerCase(); // type inference
		// this.<String>genMethTest("Test", new Object()); // explicit generic invocation - wrong parameters!
		// this.genMethTest("Test", new Object()).toLowerCase(); // type inference; this should fail
		String x[] = new String[1];
		Arrays.asList(x).get(0).toLowerCase();

		Comparator com = new Comparator() {
			public int compare(Object o1, Object o2) {
				return 0;
			}
		};
		Class cl[] = new Class[1];
		Arrays.sort(cl, com);
	}

	<T, V> List<List<Map<String, List<String>>>> foobar(T... args) {
		return null;
	}
	
	<T, V> List<List<Map<String, List<String>>>> foobar2(T[] args) {
		return null;
	}


	<T> T foo(List<T> l) {
		return l.get(0);
	}

	void dontcare() {
		List<String> l = new ArrayList<String>();
		l.add("Hmm");
		foo(l).toLowerCase(); // infer from type argument only
	}

	// intersection types
	class AA extends ArrayList implements Serializable, Iterable {
	}

	class BB implements Serializable, Iterable {
		public Iterator iterator() {
			return null;
		}
	}

	<T> T AABB(T a1, T a2) {
		AABB(new AA(), new BB()).iterator().next();
		return null;
	}
	
	class SpecializedList extends ArrayList<String> {
		void foo() {
			new SpecializedList().get(0).toUpperCase();
		}
	}
	
	class StupidList extends SpecializedList {
		void bar() {
			new StupidList().get(0).toUpperCase();
		}
	}
}

class X<A extends List> {
	A foo(A x) {
		return x;
	}
}

class Y<B extends List> extends X<B> {
	void bar(B x) {
		foo(x);
	}
}

class Z {
    public static <T extends Comparable<? super T>> void sort(List<T> list) {
		Object[] a = list.toArray();
		Arrays.sort(a);
		ListIterator<T> i = list.listIterator();
		for (int j=0; j<a.length; j++) {
	    	i.next();
		    i.set((T)a[j]);
		}
	}
}